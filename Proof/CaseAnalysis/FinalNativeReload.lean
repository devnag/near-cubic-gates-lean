import Proof.CaseAnalysis.FinalInterRowReloader
import Proof.CaseAnalysis.RowsTouchingOverwrite
import Proof.Amplification.RecoveryTapeSupport

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.ExtDecompositionBatch

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeReload

/-! ## 1. Tape lengths are monotone along every run -/

/-- One local action either leaves a tape alone or writes one cell, and `writeTapeBit`
(`Proof/Foundations/LocalBitMultitapeCore.lean`) only replaces a cell or extends the tape. -/
theorem applyAction_length {t s : ℕ} (c : Configuration t s) (a : Action t s) (i : Fin t) :
    (c.tapes i).length ≤ ((applyAction c a).tapes i).length := by
  rw [applyAction_tape_local]
  cases hw : a.write i with
  | none => exact Nat.le_refl _
  | some v =>
    rw [RecoveryTapeSupport.write_length]
    exact Nat.le_max_left _ _

theorem step_length {t s : ℕ} (m : Machine t s) (c d : Configuration t s)
    (hs : step m c = some d) (i : Fin t) : (c.tapes i).length ≤ (d.tapes i).length := by
  unfold step at hs
  obtain ⟨action, _hrule, he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  exact applyAction_length c action i

theorem runFrom_length {t s : ℕ} (m : Machine t s) :
    ∀ (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s),
      runFrom m fuel c = some r → ∀ i, (c.tapes i).length ≤ (r.final.tapes i).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro c r hr i
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact Nat.le_refl _
    · contradiction
  | succ fuel ih =>
    intro c r hr i
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact Nat.le_refl _
    · cases hstep : step m c with
      | none => simp [hstep] at hr
      | some d =>
        cases htail : runFrom m fuel d with
        | none => simp [hstep, htail] at hr
        | some tail =>
          simp only [hstep, htail, Option.some.injEq] at hr
          subst r
          exact (step_length m c d hstep i).trans (ih d tail htail i)

theorem length_mono {t s : ℕ} {m : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A B : Fin t → List Bool} (h : Step m n H A H' B) (i : Fin t) :
    (A i).length ≤ (B i).length := by
  obtain ⟨r, hr, _hh, ht, _hs⟩ := h
  have hlen := runFrom_length m n ⟨m.start, H, A⟩ r hr i
  rw [ht] at hlen
  exact hlen

/-- **The growth condition is unavoidable.**  No machine, on any tape count, can carry slot `slot`
from the cut stream of one row to the cut stream of another without the first being at most as long
as the second.  `hgrow` of `native_step` is therefore the exact condition, not a convenience. -/
theorem native_growth_necessary {u s : ℕ} {m : Machine u s} {n : ℕ} {H H' : Fin u → ℕ}
    {A B : Fin u → List Bool} (slot : Fin u) (row row' : EquationRow.Input)
    (hA : A slot = Header.stream row) (hB : B slot = Header.stream row')
    (h : Step m n H A H' B) :
    (Header.stream row).length ≤ (Header.stream row').length := by
  have hlen := length_mono h slot
  rw [hA, hB] at hlen
  exact hlen

/-! ## 2. What the length of a printed cut stream is -/

/-- Every framed sign-magnitude field of a cut is `2 * p + 3` cells long, and a cut has
`|leftWeights| + |rightWeights| + 2` fields (`MatrixScoreBatch.fields`,
`Proof/MachineModel/OrdinaryMatrixScoreBatchCodec.lean`). -/
theorem cut_word_length (pw : ℕ) (c : MatrixScoreBatch.Cut) :
    (MatrixScoreBatch.cutWord pw c).length =
      (c.leftWeights.length + c.rightWeights.length + 2) * (2 * pw + 3) := by
  simp [MatrixScoreBatch.cutWord, MatrixScoreBatch.fields, List.length_flatMap]
  ring

/-- **The length of the externally owned native word** is the row's CUT COUNT times a factor fixed
by `(d, p, odd)` alone. -/
theorem stream_length (row : EquationRow.Input) :
    (Header.stream row).length =
      row.cuts.length * ((row.d + (row.d - row.odd.toNat) + 2) * (2 * row.p + 3)) := by
  have hmap : row.cuts.map (fun c => (MatrixScoreBatch.cutWord row.p c).length) =
      row.cuts.map (fun _ => (row.d + (row.d - row.odd.toNat) + 2) * (2 * row.p + 3)) := by
    apply List.map_congr_left
    intro c hc
    obtain ⟨hl, hr⟩ := row.lengths c hc
    have hright : c.rightWeights.length = row.d - row.odd.toNat := by omega
    rw [cut_word_length, hl, hright]
  simp only [Header.stream, List.length_flatMap, hmap, List.map_const', List.sum_replicate,
    smul_eq_mul]

/-- **The chaining condition, reduced to a quantity the row names.**  For rows that agree on
`d`, `p` and `odd` — every row of one C10 supplier family does — the native tape can be rewritten
between rounds exactly when the cut count does not decrease. -/
theorem growth_iff_cuts (row row' : EquationRow.Input)
    (hd : row'.d = row.d) (hp : row'.p = row.p) (ho : row'.odd = row.odd) :
    ((Header.stream row).length ≤ (Header.stream row').length ↔
      row.cuts.length ≤ row'.cuts.length) := by
  have hk : 0 < (row.d + (row.d - row.odd.toNat) + 2) * (2 * row.p + 3) :=
    Nat.mul_pos (by omega) (by omega)
  rw [stream_length, stream_length, hd, hp, ho]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_right h hk
  · intro h
    exact Nat.mul_le_mul_right _ h

/-! ## 3. The writer's tape space: the reloader's, plus the next row's cut stream and its driver -/

/-- `C10InterRowReloader.tapes p` (`Proof/CaseAnalysis/FinalInterRowReloader.lean`) plus two
retained ports. -/
def tapes (p : Program) : ℕ := C10InterRowReloader.tapes p + 2

/-- The reloader's whole tape space, embedded unchanged. -/
def old (p : Program) (i : Fin (C10InterRowReloader.tapes p)) : Fin (tapes p) := i.castAdd 2

/-- The port that carries the NEXT row's printed cut stream. -/
def wordPort (p : Program) : Fin (tapes p) :=
  (0 : Fin 2).natAdd (C10InterRowReloader.tapes p)

/-- The port that carries the paid unary driver word of the write. -/
def drivePort (p : Program) : Fin (tapes p) :=
  (1 : Fin 2).natAdd (C10InterRowReloader.tapes p)

/-- Slot `52`, the externally owned native cut tape. -/
def nativeSlot (p : Program) : Fin (tapes p) :=
  old p (C10InterRowReloader.bank p (Reuse.native p))

/-- The estimator bank's own rewind log, reused as the write's rewind log. -/
def logSlot (p : Program) : Fin (tapes p) :=
  old p (C10InterRowReloader.bank p (Reuse.log p))

theorem word_val (p : Program) : (wordPort p).val = C10InterRowReloader.tapes p := rfl

theorem drive_val (p : Program) : (drivePort p).val = C10InterRowReloader.tapes p + 1 := rfl

theorem native_slot_val (p : Program) : (nativeSlot p).val = 52 := rfl

theorem log_slot_val (p : Program) : (logSlot p).val = WholePrefix.tapes p := rfl

theorem reloader_tapes_val (p : Program) :
    C10InterRowReloader.tapes p = WholePrefix.tapes p + 1 + 2 + (WholePrefix.tapes p - 2) := rfl

/-- The dock of the write: the word port, slot `52`, the driver word, the rewind log — in
`RecoveryBoundedTapeCopy`'s own tape order (`Proof/Amplification/RecoveryBoundedTapeCopy.lean`). -/
def slots (p : Program) : Fin 4 → Fin (tapes p) :=
  ![wordPort p, nativeSlot p, drivePort p, logSlot p]

theorem at_word (p : Program) : slots p 0 = wordPort p := rfl
theorem at_native (p : Program) : slots p 1 = nativeSlot p := rfl
theorem at_drive (p : Program) : slots p 2 = drivePort p := rfl
theorem at_log (p : Program) : slots p 3 = logSlot p := rfl

theorem slots_val (p : Program) (j : Fin 4) :
    (slots p j).val = ![C10InterRowReloader.tapes p, 52, C10InterRowReloader.tapes p + 1,
      WholePrefix.tapes p] j := by
  fin_cases j <;> rfl

theorem slots_injective (p : Program) : Function.Injective (slots p) := by
  have hn := C10InterRowReloader.prefix_wide p
  have ht := reloader_tapes_val p
  intro i j he
  have hv : (slots p i).val = (slots p j).val := congrArg Fin.val he
  rw [slots_val p i, slots_val p j] at hv
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at hv <;> omega)

/-! ## 4. The writer -/

/-- **The writer.**  One docked run of `RecoveryBoundedTapeCopy.machine`
(`Proof/Amplification/RecoveryBoundedTapeCopy.lean`) over the four slots of `slots`. -/
noncomputable def machine (p : Program) :=
  RecoveryFocus.machine (slots p) RecoveryBoundedTapeCopy.machine

theorem native_step (p : Program) (row row' : EquationRow.Input) (D : ℕ)
    (H : Fin (tapes p) → ℕ) (A : Fin (tapes p) → List Bool)
    (hgrow : (Header.stream row).length ≤ (Header.stream row').length)
    (hfit : (Header.stream row').length ≤ D)
    (hwh : H (wordPort p) = 0) (hnh : H (nativeSlot p) = 0)
    (hdh : H (drivePort p) = 0) (hlh : H (logSlot p) = 0)
    (hword : A (wordPort p) = Header.stream row')
    (hnative : A (nativeSlot p) = Header.stream row)
    (hdrive : A (drivePort p) = List.replicate (Header.stream row').length true)
    (hlog : A (logSlot p) = List.replicate (D + 1) false) :
    ∃ B, Step (machine p) (2 * (Header.stream row').length + 4) H A H B ∧
      B (nativeSlot p) = Header.stream row' ∧
      B (wordPort p) = Header.stream row' ∧
      B (drivePort p) = List.replicate (Header.stream row').length true ∧
      B (logSlot p) = List.replicate (D + 1) false ∧
      (∀ i, (∀ j, slots p j ≠ i) → B i = A i) := by
  obtain ⟨r, hr, hh, ht, hs⟩ :=
    (CloseoutRowsTouching.Overwrite.ready (Header.stream row') (Header.stream row)
        (Header.stream row').length (D + 1) rfl hgrow (by omega)).focus_at
      (slots p) (slots_injective p) H A
      (by
        intro j
        fin_cases j
        · exact hword
        · exact hnative
        · exact hdrive
        · exact hlog)
      (by
        intro j
        fin_cases j
        · exact hwh
        · exact hnh
        · exact hdh
        · exact hlh)
  refine ⟨install (slots p) A
      ![Header.stream row', Header.stream row',
        List.replicate (Header.stream row').length true, List.replicate (D + 1) false],
    ⟨r, hr, hh, ht, le_of_eq hs⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← at_native p, install_slot _ (slots_injective p)]
    rfl
  · rw [← at_word p, install_slot _ (slots_injective p)]
    rfl
  · rw [← at_drive p, install_slot _ (slots_injective p)]
    rfl
  · rw [← at_log p, install_slot _ (slots_injective p)]
    rfl
  · intro i hi
    exact install_other _ _ _ _ hi

/-! ## 5. The same conclusion in the consumer's vocabulary -/

theorem native_run {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (row row' : EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row').U → Fin (EquationRow.request row').U → Bool)
    (E D : ℕ) (out : List Bool)
    (H : Fin (tapes p) → ℕ) (A : Fin (tapes p) → List Bool)
    (hgrow : (Header.stream row).length ≤ (Header.stream row').length)
    (hfit : (Header.stream row').length ≤ D)
    (hwh : H (wordPort p) = 0) (hnh : H (nativeSlot p) = 0)
    (hdh : H (drivePort p) = 0) (hlh : H (logSlot p) = 0)
    (hword : A (wordPort p) = Header.stream row')
    (hnative : A (nativeSlot p) = Header.stream row)
    (hdrive : A (drivePort p) = List.replicate (Header.stream row').length true)
    (hlog : A (logSlot p) = List.replicate (D + 1) false) :
    ∃ B, Step (machine p) (2 * (Header.stream row').length + 4) H A H B ∧
      B (nativeSlot p) =
        (WarmReuse.entry p worker E (Warm.input p row' C Q q denominator select) out).tapes
          (Reuse.native p) ∧
      B (logSlot p) = List.replicate (D + 1) false ∧
      (∀ i, (∀ j, slots p j ≠ i) → B i = A i) := by
  obtain ⟨B, hstep, hnat, _hw, _hd, hl, hother⟩ :=
    native_step p row row' D H A hgrow hfit hwh hnh hdh hlh hword hnative hdrive hlog
  refine ⟨B, hstep, ?_, hl, hother⟩
  rw [hnat, C10InterRowReloader.entry_native p worker row' C Q q denominator select E out]

/-! ## 6. The reloader and the writer as ONE machine -/

/-- The reloader (`C10InterRowReloader.machine`,
`Proof/CaseAnalysis/FinalInterRowReloader.lean`) embedded over the two new ports, then the
writer. -/
noncomputable def full (p : Program) :=
  Composition.machine (TapeEmbedding.machine 2 (C10InterRowReloader.machine p)) (machine p)

theorem heads_split (p : Program) (H : Fin (tapes p) → ℕ) :
    Fin.addCases (motive := fun _ => ℕ) (fun i => H (old p i))
        (fun j : Fin 2 => H (j.natAdd (C10InterRowReloader.tapes p))) = H := by
  funext i
  refine Fin.addCases (m := C10InterRowReloader.tapes p) (n := 2) (fun k => ?_) (fun k => ?_) i
  · simp only [Fin.addCases_left]
    rfl
  · simp only [Fin.addCases_right]

theorem tapes_split (p : Program) (A : Fin (tapes p) → List Bool) :
    Fin.addCases (motive := fun _ => List Bool) (fun i => A (old p i))
        (fun j : Fin 2 => A (j.natAdd (C10InterRowReloader.tapes p))) = A := by
  funext i
  refine Fin.addCases (m := C10InterRowReloader.tapes p) (n := 2) (fun k => ?_) (fun k => ?_) i
  · simp only [Fin.addCases_left]
    rfl
  · simp only [Fin.addCases_right]

/-- **The discharge.**  ONE `Step` of ONE machine takes the configuration `WarmActual.run`
(`Proof/CaseAnalysis/RowsEstimatorActual.lean`) exits in — blanked work tapes, the paid driver
word, the rewind log, and the cut stream of the row it just ran on slot `52` — to round `k+1`'s
ENTRY configuration on the whole reusable bank: `WarmReuse.padded p D (Warm.input p row' …)` on
every `Reuse.work` slot AND `Header.stream row'` on slot `52`. -/
theorem reload_native_step (p : Program) (row row' : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row').U → Fin (EquationRow.request row').U → Bool)
    (D : ℕ) (H : Fin (tapes p) → ℕ) (A : Fin (tapes p) → List Bool)
    (hgrow : (Header.stream row).length ≤ (Header.stream row').length)
    (hfit : (Header.stream row').length ≤ D)
    (hrow : ∀ i, (C10InterRowReloader.rowData p row' C Q q denominator select i).length ≤ D)
    (hph : ∀ i, H (old p (C10InterRowReloader.port p i)) = 0)
    (hwh : ∀ i, H (old p (C10InterRowReloader.bank p (Reuse.work p i))) = 0)
    (hdh : H (old p (C10InterRowReloader.bank p (Reuse.driver p))) = 0)
    (hlh : H (logSlot p) = 0) (hnh : H (nativeSlot p) = 0)
    (hwordh : H (wordPort p) = 0) (hdriveh : H (drivePort p) = 0)
    (hport : ∀ i, A (old p (C10InterRowReloader.port p i)) =
      C10InterRowReloader.rowData p row' C Q q denominator select i)
    (hwork : ∀ i, A (old p (C10InterRowReloader.bank p (Reuse.work p i))) =
      List.replicate D false)
    (hdriver : A (old p (C10InterRowReloader.bank p (Reuse.driver p))) = List.replicate D true)
    (hlog : A (logSlot p) = List.replicate (D + 1) false)
    (hnative : A (nativeSlot p) = Header.stream row)
    (hword : A (wordPort p) = Header.stream row')
    (hdrive : A (drivePort p) = List.replicate (Header.stream row').length true) :
    ∃ B, Step (full p) (2 * D + 4 + 1 + (2 * (Header.stream row').length + 4)) H A H B ∧
      (∀ i, B (old p (C10InterRowReloader.bank p (Reuse.work p i))) =
        WarmReuse.padded p D (Warm.input p row' C Q q denominator select)
          (C10InterRowReloader.rowIndex p i)) ∧
      B (nativeSlot p) = Header.stream row' ∧
      B (old p (C10InterRowReloader.bank p (Reuse.driver p))) = List.replicate D true ∧
      B (logSlot p) = List.replicate (D + 1) false := by
  obtain ⟨B0, hstep0, hwork0, hdriver0, hlog0, hport0, hother0⟩ :=
    C10InterRowReloader.reload_step p row' C Q q denominator select D
      (fun i => H (old p i)) (fun i => A (old p i)) hrow hph hwh hdh hlh hport hwork hdriver hlog
  have hnative0 : B0 (C10InterRowReloader.bank p (Reuse.native p)) = Header.stream row :=
    (hother0 _ (C10InterRowReloader.reload_avoids_native p)).trans hnative
  have hembed := (hstep0.embed (fun j : Fin 2 => H (j.natAdd (C10InterRowReloader.tapes p)))
    (fun j : Fin 2 => A (j.natAdd (C10InterRowReloader.tapes p)))).congr_in
      (heads_split p H) (tapes_split p A)
  obtain ⟨B, hstep1, hnat, _hw, _hd, hl, hother⟩ :=
    native_step p row row' D
      (Fin.addCases (motive := fun _ => ℕ) (fun i => H (old p i))
        (fun j : Fin 2 => H (j.natAdd (C10InterRowReloader.tapes p))))
      (Fin.addCases (motive := fun _ => List Bool) B0
        (fun j : Fin 2 => A (j.natAdd (C10InterRowReloader.tapes p))))
      hgrow hfit
      (by simp only [wordPort, Fin.addCases_right]; exact hwordh)
      (by simp only [nativeSlot, old, Fin.addCases_left]; exact hnh)
      (by simp only [drivePort, Fin.addCases_right]; exact hdriveh)
      (by simp only [logSlot, old, Fin.addCases_left]; exact hlh)
      (by simp only [wordPort, Fin.addCases_right]; exact hword)
      (by simp only [nativeSlot, old, Fin.addCases_left]; exact hnative0)
      (by simp only [drivePort, Fin.addCases_right]; exact hdrive)
      (by simp only [logSlot, old, Fin.addCases_left]; exact hlog0)
  refine ⟨B, (hembed.seq hstep1).congr (heads_split p H) rfl, ?_, hnat, ?_, hl⟩
  · intro i
    have hne : ∀ j, slots p j ≠ old p (C10InterRowReloader.bank p (Reuse.work p i)) := by
      have hn := C10InterRowReloader.prefix_wide p
      have ht := reloader_tapes_val p
      have hb := Reuse.work_bounds p i
      intro j he
      have hv : (slots p j).val = (Reuse.work p i).val := congrArg Fin.val he
      rw [slots_val p j] at hv
      fin_cases j <;> simp at hv <;> omega
    rw [hother _ hne]
    simp only [old, Fin.addCases_left]
    exact hwork0 i
  · have hne : ∀ j, slots p j ≠ old p (C10InterRowReloader.bank p (Reuse.driver p)) := by
      have hn := C10InterRowReloader.prefix_wide p
      have ht := reloader_tapes_val p
      intro j he
      have hv : (slots p j).val = WholePrefix.tapes p + 2 := congrArg Fin.val he
      rw [slots_val p j] at hv
      fin_cases j <;> simp at hv <;> omega
    rw [hother _ hne]
    simp only [old, Fin.addCases_left]
    exact hdriver0

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeReload

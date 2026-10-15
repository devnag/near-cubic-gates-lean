import Proof.CaseAnalysis.FinalSupplierCountStage
import Proof.CaseAnalysis.RowsProjectionReset

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank bankAt)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **The zeroed tape IS the padded empty tape.**  `RecoveryScratchErase`'s exit
shape and `ZeroPadding`'s padding are the same list. -/
theorem pad_nil (total : ℕ) : ZeroPadding.pad total [] = List.replicate total false := rfl

/-- The padded ZEROED tape is again the zeroed tape, at any capacity the band
already covers -- so the discipline is stable under a second padding. -/
theorem pad_zeroed (total cap : ℕ) (h : total ≤ cap) :
    ZeroPadding.pad cap (List.replicate total false) = List.replicate cap false :=
  pad_replicate_false cap total h

/-! ## §2  The band, and the fictional bank the docks are run in

`install slots A (fun _ => [])` (`Proof/Amplification/RecoveryReadyCalls.lean`) is the bank
in which the round's slots are literally empty.  Every docked engine applies to
it with NO hypothesis on `A` at all.  `bandCap` pads exactly those slots back up
to the real, zeroed band, and pads nothing else. -/

/-- **The `k`-FREE band invariant.**  Contrast APPENDS's
`fun k s => BlankFrom (line + k * block) s`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`), whose line MOVES and which
`band_exhausted` (`Proof/CaseAnalysis/FinalPrologueBlankBand.lean`) therefore
exhausts.  `line` here does not depend on the round index. -/
def ZeroBand (total line : ℕ) (s : ℕ → List Bool) : Prop :=
  ∀ v : ℕ, line ≤ v → s v = List.replicate total false

/-- `BlankFrom` is `ZeroBand` at `total = 0`, so nothing APPENDS proved is lost. -/
theorem blankFrom_zeroBand (line : ℕ) (s : ℕ → List Bool)
    (h : RepairSource.CloseoutFinal.C10SupplierCountStage.BlankFrom line s) :
    ZeroBand 0 line s := by
  intro v hv
  simpa using h v hv

/-- The capacity vector that repads the round's slots and nothing else.  Built
from `RecoveryFocus.pick` (`Proof/Amplification/RecoveryFocusedMachine.lean`), the same
selector `install` (`Proof/Amplification/RecoveryReadyCalls.lean`) uses, so the two agree
slot for slot. -/
noncomputable def bandCap {t r : ℕ} (slots : Fin r → Fin t) (total : ℕ) : Fin t → ℕ :=
  fun i => match RecoveryFocus.pick slots i with | some _ => total | none => 0

theorem bandCap_slot {t r : ℕ} (slots : Fin r → Fin t) (hinj : Function.Injective slots)
    (total : ℕ) (j : Fin r) : bandCap slots total (slots j) = total := by
  simp [bandCap, RecoveryFocus.pick_slot slots hinj]

theorem bandCap_other {t r : ℕ} (slots : Fin r → Fin t) (total : ℕ) (i : Fin t)
    (hi : ∀ j, slots j ≠ i) : bandCap slots total i = 0 := by
  classical
  have hn : ¬ ∃ j, slots j = i := by
    rintro ⟨j, hj⟩
    exact hi j hj
  simp [bandCap, RecoveryFocus.pick, hn]

/-- The capacity never exceeds the band's own length budget. -/
theorem bandCap_le {t r : ℕ} (slots : Fin r → Fin t) (total : ℕ) (i : Fin t) :
    bandCap slots total i ≤ total := by
  unfold bandCap
  split <;> omega

/-- **The docked-engine hypothesis, supplied with NO hypothesis on the bank.**
`dock` (`Proof/CaseAnalysis/FinalWordFunctionDock.lean`), `clause_dock`
(`:267`), `support_dock` (`:286`), `sum_dock`
(`Proof/CaseAnalysis/FinalWordEngines.lean`), `copy_dock` (`:90`),
`product_dock` (`:120`), `fixedWord_dock` (`:161`), `divide_dock`
(`Proof/CaseAnalysis/FinalDividerDock.lean`) and `answer_dock` (`:141`) all
demand `A (slots j) = []`; here it is, at every round, forever. -/
theorem blank_at_slots {t r : ℕ} (slots : Fin r → Fin t) (hinj : Function.Injective slots)
    (A : Fin t → List Bool) (j : Fin r) :
    install slots A (fun _ : Fin r => []) (slots j) = [] :=
  install_slot slots hinj A (fun _ : Fin r => []) j

/-- Off the slots the fictional bank IS the real one. -/
theorem blank_off_slots {t r : ℕ} (slots : Fin r → Fin t) (A : Fin t → List Bool)
    (i : Fin t) (hi : ∀ j, slots j ≠ i) :
    install slots A (fun _ : Fin r => []) i = A i :=
  install_other slots A (fun _ : Fin r => []) i hi

/-- **The `k`-free invariant is NOT the vacuous one.**  Dual of
`blankFrom_above_bank_certifies_nothing`
(`Proof/CaseAnalysis/FinalPrologueBlankBand.lean`), which says an invariant
stated at or above the bank width is free AND certifies no bank tape blank:
`ZeroBand` at a line INSIDE the bank pins every band tape of the bank to the
padded empty tape. -/
theorem zeroBand_certifies {t : ℕ} (total line : ℕ) (hline : 278 ≤ line)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : ZeroBand total line s) (i : Fin t) (hi : line ≤ i.val) :
    bank stream count driver input witness s i = ZeroPadding.pad total [] := by
  rw [RepairSource.CloseoutFinal.C10SupplierCountStage.bank_scratch_apply stream count driver
      input witness s i (le_trans hline hi), hs i.val hi, pad_nil]

/-- **The fictional bank, repadded, IS the real bank.**  This is where `ZeroBand`
is spent, and the only place it is spent. -/
theorem pad_install_blank {t r : ℕ} (total line : ℕ) (hline : 278 ≤ line)
    (slots : Fin r → Fin t) (hinj : Function.Injective slots)
    (hband : ∀ j, line ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : ZeroBand total line s) :
    (fun i => ZeroPadding.pad (bandCap slots total i)
        (install slots (bank stream count driver input witness s) (fun _ : Fin r => []) i))
      = bank stream count driver input witness s := by
  classical
  funext i
  by_cases hi : ∃ j, slots j = i
  · obtain ⟨j, hj⟩ := hi
    subst hj
    rw [bandCap_slot slots hinj total j, blank_at_slots slots hinj _ j, pad_nil,
      RepairSource.CloseoutFinal.C10SupplierCountStage.bank_scratch_apply stream count driver
        input witness s (slots j) (le_trans hline (hband j)),
      hs (slots j).val (hband j)]
  · have hi' : ∀ j, slots j ≠ i := by
      intro j hj
      exact hi ⟨j, hj⟩
    rw [bandCap_other slots total i hi', blank_off_slots slots _ i hi',
      ZeroPadding.pad_zero]

/-! ## §3  The deliverable: one round of the loop, over a RECYCLED band -/

/-- **ONE ROUND, OVER A BAND THAT IS REUSED.**

`hstep` is what the docked-engine library gives: a `Step` of the round body out
of the bank whose slots are literally `[]`, supplied by `blank_at_slots` with no
hypothesis.  `hframe` is the frame clause every one of the nine docks carries.
The conclusion is a `Step` of the SAME machine at the SAME fuel between two REAL
banks, in exactly the shape `Rounds`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) demands.

**Nothing in the statement moves with the round index.**  `line` is fixed,
`total` is fixed, `extra` is fixed, and the slots are the SAME slots at every
round.  That is the whole point: `band_exhausted` applies to a moving line and
there is no moving line here. -/
theorem round_step_of_zeroBand (extra total line cost : ℕ) (hline : 278 ≤ line)
    {bs r : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (slots : Fin r → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, line ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : ZeroBand total line s)
    (H' : Fin (218 + (60 + extra)) → ℕ) (B : Fin (218 + (60 + extra)) → List Bool)
    (hstep : Step body cost (fun _ => 0)
      (install slots (bank stream count driver input witness s) (fun _ : Fin r => [])) H' B)
    (hzero : ∀ i, H' i = 0)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      B i = install slots (bank stream count driver input witness s)
        (fun _ : Fin r => []) i) :
    Step body cost (fun _ => 0) (bank stream count driver input witness s) (fun _ => 0)
      (bank stream count driver input witness
        (RepairSource.CloseoutFinal.C10SupplierCountStage.scratchOf extra
          (fun i => ZeroPadding.pad (bandCap slots total i) (B i)) s)) := by
  have hpad := Step.pad hstep (bandCap slots total)
  rw [pad_install_blank total line hline slots hinj hband stream count driver input witness s hs]
    at hpad
  refine RepairSource.CloseoutFinal.C10SupplierCountStage.round_step_of_dock extra cost
    stream count driver input witness s slots (fun j => le_trans hline (hband j)) H'
    (fun i => ZeroPadding.pad (bandCap slots total i) (B i)) hpad hzero ?_
  intro i hi
  rw [bandCap_other slots total i hi, ZeroPadding.pad_zero, hframe i hi,
    blank_off_slots slots _ i hi]

theorem exit_off_slots {t r : ℕ} (slots : Fin r → Fin t) (total : ℕ)
    (B : Fin t → List Bool) (i : Fin t) (hi : ∀ j, slots j ≠ i) :
    ZeroPadding.pad (bandCap slots total i) (B i) = B i := by
  rw [bandCap_other slots total i hi, ZeroPadding.pad_zero]

/-! ## §4  The band is restored, and the length bound that lets it be -/

/-- **The clear pass, as a `Step`.**  Arbitrary dirt in, `List.replicate total
false` out, its own unary driver handed back unchanged, at `2 * total + 4`
steps.  This is `RecoveryScratchErase.erase_ready`
(`Proof/Amplification/RecoveryScratchErase.lean`) in the batch's `Step` vocabulary; no new
machine is built here. -/
theorem clear_step {t : ℕ} (total capacity : ℕ) (backing : Fin t → List Bool)
    (hb : ∀ i, (backing i).length ≤ total) :
    Step (RecoveryScratchErase.resetMachine t) (2 * total + 4) (fun _ => 0)
      (Fin.addCases (Fin.addCases backing (fun _ : Fin 1 => List.replicate total true))
        (fun _ : Fin 1 => List.replicate capacity false))
      (fun _ => 0)
      (Fin.addCases (Fin.addCases (fun _ : Fin t => List.replicate total false)
        (fun _ : Fin 1 => List.replicate total true))
        (fun _ : Fin 1 => List.replicate (max capacity (total + 1)) false)) :=
  Step.of_ready (RecoveryScratchErase.erase_ready total capacity backing hb)

/-- **The clear pass's own workspace is a FIXED POINT.**  At
`capacity := total + 1` the log tape comes back exactly as it went in, and the
driver tape is returned unchanged by `clear_step` itself, so the entry layout is
re-established for the next round.  There is no growth anywhere. -/
theorem clear_capacity_fixed (total : ℕ) : max (total + 1) (total + 1) = total + 1 :=
  Nat.max_self _

/-- **The length bound is a CONSEQUENCE of the round budget, not a new
assumption.**  A band tape entering a round at length at most `total` with its
head at `0` leaves it at length at most `total`, as long as the round's step
count plus one fits in `total`.  This is
`CloseoutRowsProjectionReset.scratch_support`
(`Proof/CaseAnalysis/RowsProjectionReset.lean`) in `Step` vocabulary. -/
theorem band_length_after_round {t s : ℕ} (M : Machine t s) (cost total : ℕ)
    {H H' : Fin t → ℕ} {A B : Fin t → List Bool} (h : Step M cost H A H' B)
    (hcost : cost + 1 ≤ total) (i : Fin t) (hh : H i = 0) (ht : (A i).length ≤ total) :
    (B i).length ≤ total := by
  obtain ⟨rr, hr, _hh, htapes, hs⟩ := h
  have hsupp := CloseoutRowsProjectionReset.scratch_support M cost total
    ⟨M.start, H, A⟩ rr hr i hh ht (by omega)
  rw [htapes] at hsupp
  exact hsupp

/-- **`total := cost + 1` closes the loop.**  The bound does not grow with the
round index, so `clear_step`'s `hb` holds at every round with the SAME `total`
and the SAME band. -/
theorem band_length_at_cost {t s : ℕ} (M : Machine t s) (cost : ℕ)
    {H H' : Fin t → ℕ} {A B : Fin t → List Bool} (h : Step M cost H A H' B)
    (i : Fin t) (hh : H i = 0) (ht : (A i).length ≤ cost + 1) :
    (B i).length ≤ cost + 1 :=
  band_length_after_round M cost (cost + 1) h (Nat.le_refl _) i hh ht

/-- The entry length bound, read straight off the invariant. -/
theorem zeroBand_length {t : ℕ} (total line : ℕ) (hline : 278 ≤ line)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : ZeroBand total line s) (i : Fin t) (hi : line ≤ i.val) :
    (bank stream count driver input witness s i).length ≤ total := by
  rw [RepairSource.CloseoutFinal.C10SupplierCountStage.bank_scratch_apply stream count driver
      input witness s i (le_trans hline hi), hs i.val hi, List.length_replicate]

/-- **The round's exit band is still inside the clear pass's reach.**  The exit
at a slot is `pad total (B i)`, whose length is at most `total` once the round's
own budget is at most `total - 1`.  This is the hypothesis `clear_step` needs,
discharged. -/
theorem exit_length_at_slots {t s r : ℕ} (M : Machine t s) (cost total : ℕ)
    (hcost : cost + 1 ≤ total) (slots : Fin r → Fin t)
    {H H' : Fin t → ℕ} {A B : Fin t → List Bool} (h : Step M cost H A H' B)
    (hh : ∀ i, H i = 0) (ht : ∀ i, (A i).length ≤ total) (i : Fin t) :
    (ZeroPadding.pad (bandCap slots total i) (B i)).length ≤ total := by
  rw [ZeroPadding.pad_length]
  have h1 := band_length_after_round M cost total h hcost i (hh i) (ht i)
  have h2 : bandCap slots total i ≤ total := bandCap_le slots total i
  omega

theorem moving_band_exhausted (line block width : ℕ) (hblock : 1 ≤ block) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → width ≤ line + k * block := by
  refine ⟨width, fun k hk => ?_⟩
  have hmul : width * 1 ≤ k * block := Nat.mul_le_mul hk hblock
  omega

/-- **A fixed band is not.**  The invariant at round `k` is the invariant at
round `0` for every `k`, so there is no `K` past which it degenerates -- and
`zeroBand_certifies` shows it is not vacuous either. -/
theorem fixed_band_uniform (total line : ℕ) (s : ℕ → List Bool) (k : ℕ) :
    (fun (_ : ℕ) (w : ℕ → List Bool) => ZeroBand total line w) k s
      ↔ (fun (_ : ℕ) (w : ℕ → List Bool) => ZeroBand total line w) 0 s :=
  Iff.rfl

end NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle

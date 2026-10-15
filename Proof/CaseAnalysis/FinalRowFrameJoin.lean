import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmRetained
import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.CaseAnalysis.FinalRowOrdering
import Proof.CaseAnalysis.FinalRoundBudget

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RepairOrdinary.C10RowFrameJoin

open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CloseoutRowsEstimator
open CompetitorCrossScheduler (producer)
open NearCubicWires.ExtDecompositionBatch (Step dockH)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
  (familyWriter familyFuel familyStream wordList pairList pairWord pairValue familyDenominator
    family_run)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule (widthPower)
open NearCubicWires.RepairSource.CloseoutFinal.C10RowOrdering
  (Round orderedPairList orderedWordList orderedFamilyStream orderedRow orderedPairList_growth
    ordered_family_run)

/-! ## 1. The reusable estimator bank's tape cover

`Reuse.tapes p` is `WholePrefix.tapes p + 1 + 2` and is partitioned by the five named slots plus
the `work` family; `WarmReuse.run` pins the heads everywhere and the tapes on `output`, `work`,
`driver` and `log`, while `WarmActual.native_run`/`capacity_run` pin the remaining two.  The cover
below is what turns those pins into a TOTAL exit tape function. -/

theorem slot_ne {p : Program} {i j : Fin (Reuse.tapes p)} (h : i.val ≠ j.val) : i ≠ j :=
  fun he => h (congrArg Fin.val he)

theorem tapes_ge (p : Program) : 70 ≤ WholePrefix.tapes p := by
  unfold WholePrefix.tapes; omega

theorem output_val (p : Program) : (Reuse.output p).val = WholePrefix.tapes p + 1 := by
  simp [Reuse.output]

theorem driver_val (p : Program) : (Reuse.driver p).val = WholePrefix.tapes p + 2 := by
  simp [Reuse.driver]

theorem log_val (p : Program) : (Reuse.log p).val = WholePrefix.tapes p := by
  simp [Reuse.log]

theorem native_val (p : Program) : (Reuse.native p).val = 52 := by
  simp [Reuse.native, Reuse.old]

theorem capacity_val (p : Program) : (Reuse.capacity p).val = 68 := by
  simp [Reuse.capacity, Reuse.old, Retained.capacity]

/-- `Reuse.work_val` (`Proof/CaseAnalysis/RowsEstimatorReuseLayout.lean`) at an explicit index. -/
theorem work_val_mk (p : Program) (v : ℕ) (h : v < WholePrefix.tapes p - 2) :
    (Reuse.work p ⟨v, h⟩).val = if v < 52 then v else if v < 67 then v + 1 else v + 2 :=
  Reuse.work_val p ⟨v, h⟩

/-- **Every tape of the reusable bank is one of the six.**  This is what makes the exit tape
function of section 3 TOTAL rather than a list of pins. -/
theorem bank_cover (p : Program) (i : Fin (Reuse.tapes p)) :
    i = Reuse.output p ∨ i = Reuse.driver p ∨ i = Reuse.log p ∨
      i = Reuse.native p ∨ i = Reuse.capacity p ∨ ∃ j, i = Reuse.work p j := by
  have hT : 70 ≤ WholePrefix.tapes p := tapes_ge p
  have hi : i.val < WholePrefix.tapes p + 1 + 2 := by
    have h := i.isLt; unfold Reuse.tapes at h; omega
  have ho := output_val p
  have hd := driver_val p
  have hl := log_val p
  have hn := native_val p
  have hc := capacity_val p
  by_cases h1 : i.val = WholePrefix.tapes p + 1
  · exact Or.inl (Fin.ext (by omega))
  by_cases h2 : i.val = WholePrefix.tapes p + 2
  · exact Or.inr (Or.inl (Fin.ext (by omega)))
  by_cases h3 : i.val = WholePrefix.tapes p
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))
  by_cases h4 : i.val = 52
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by omega)))))
  by_cases h5 : i.val = 68
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  by_cases h6 : i.val < 52
  · refine ⟨⟨i.val, by omega⟩, Fin.ext ?_⟩
    rw [work_val_mk]
    split_ifs
    all_goals omega
  by_cases h7 : i.val < 68
  · refine ⟨⟨i.val - 1, by omega⟩, Fin.ext ?_⟩
    rw [work_val_mk]
    split_ifs
    all_goals omega
  · refine ⟨⟨i.val - 2, by omega⟩, Fin.ext ?_⟩
    rw [work_val_mk]
    split_ifs
    all_goals omega

/-! ## 2. The bank's entry and exit configurations, as named total functions -/

/-- The bank's head function: every head at `0` except the accumulator, which sits at the end of
the stream written so far.  `WarmReuse.run`'s conclusion is stated at exactly this function, so
entry and exit of a round differ only in the accumulated word. -/
noncomputable def bankHeads (p : Program) (out : List Bool) : Fin (Reuse.tapes p) → ℕ :=
  fun i => if i = Reuse.output p then out.length else 0

/-- **The bank's exit tapes.**  The accumulator carries the stream, the driver and reset log are at
their canonical fills, the two retained slots still carry their entry words, and every work tape is
blank — `List.replicate D false`, which is observationally `[]`
(`Proof/Foundations/LocalBitMultitapeCore.lean`). -/
noncomputable def exitTapes (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) : Fin (Reuse.tapes p) → List Bool :=
  fun i =>
    if i = Reuse.output p then out
    else if i = Reuse.driver p then List.replicate D true
    else if i = Reuse.log p then List.replicate (D + 1) false
    else if i = Reuse.native p then A (NativeReadOnly.slot p)
    else if i = Reuse.capacity p then A (Retained.capacity p)
    else List.replicate D false

/-- The bank's entry head function, unfolded once at the function level.  Stating it as a
function rather than at an applied index is what keeps the `Fin.addCases` decision procedure from
being asked to reduce `WholePrefix.tapes p + 1 + 0 < WholePrefix.tapes p + 1` on a symbolic
`p`. -/
theorem entry_heads_fun {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) :
    (WarmReuse.entry p worker D A out).heads =
      Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin (WholePrefix.tapes p + 1) => 0)
        (![out.length, 0] : Fin 2 → ℕ) := rfl

/-- The bank's entry tape function, unfolded once at the function level. -/
theorem entry_tapes_fun {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) :
    (WarmReuse.entry p worker D A out).tapes =
      Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool) (WarmReuse.padded p D A)
          (fun _ : Fin 1 => List.replicate (D + 1) false))
        (![out, List.replicate D true] : Fin 2 → List Bool) := rfl

theorem entry_heads {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) :
    (WarmReuse.entry p worker D A out).heads = bankHeads p out := by
  have hT := tapes_ge p
  rw [entry_heads_fun]
  funext i
  by_cases hlt : i.val < WholePrefix.tapes p + 1
  · obtain ⟨v, hv⟩ : ∃ v : Fin (WholePrefix.tapes p + 1), i = Fin.castAdd 2 v :=
      ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    subst hv
    have hne : (Fin.castAdd 2 v : Fin (Reuse.tapes p)) ≠ Reuse.output p := by
      refine slot_ne ?_
      rw [output_val]
      have hvv : (Fin.castAdd 2 v : Fin (Reuse.tapes p)).val = v.val := rfl
      rw [hvv]
      have := v.isLt
      omega
    rw [Fin.addCases_left]
    show (0 : ℕ) = bankHeads p out (Fin.castAdd 2 v)
    simp only [bankHeads]
    exact (if_neg hne).symm
  · have hi : i.val < WholePrefix.tapes p + 1 + 2 := by
      have h := i.isLt; omega
    by_cases hoi : i.val = WholePrefix.tapes p + 1
    · have he : i = Reuse.output p := Fin.ext (by rw [output_val]; exact hoi)
      subst he
      show Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin (WholePrefix.tapes p + 1) => 0)
          (![out.length, 0] : Fin 2 → ℕ) (Fin.natAdd (WholePrefix.tapes p + 1) (0 : Fin 2))
        = bankHeads p out (Reuse.output p)
      rw [Fin.addCases_right]
      simp [bankHeads]
    · have he : i = Reuse.driver p := Fin.ext (by rw [driver_val]; omega)
      subst he
      have hne : Reuse.driver p ≠ Reuse.output p :=
        slot_ne (by rw [driver_val, output_val]; omega)
      show Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin (WholePrefix.tapes p + 1) => 0)
          (![out.length, 0] : Fin 2 → ℕ) (Fin.natAdd (WholePrefix.tapes p + 1) (1 : Fin 2))
        = bankHeads p out (Reuse.driver p)
      rw [Fin.addCases_right]
      show (0 : ℕ) = bankHeads p out (Reuse.driver p)
      simp only [bankHeads]
      exact (if_neg hne).symm

theorem entry_output {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) :
    (WarmReuse.entry p worker D A out).tapes (Reuse.output p) = out := by
  rw [entry_tapes_fun]
  show Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (WarmReuse.padded p D A)
      (fun _ : Fin 1 => List.replicate (D + 1) false))
    (![out, List.replicate D true] : Fin 2 → List Bool)
    (Fin.natAdd (WholePrefix.tapes p + 1) (0 : Fin 2)) = out
  rw [Fin.addCases_right]
  rfl

theorem entry_old {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool)
    (j : Fin (WholePrefix.tapes p)) :
    (WarmReuse.entry p worker D A out).tapes (Reuse.old p j) = WarmReuse.padded p D A j := by
  rw [entry_tapes_fun]
  show Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (WarmReuse.padded p D A)
      (fun _ : Fin 1 => List.replicate (D + 1) false))
    (![out, List.replicate D true] : Fin 2 → List Bool)
    (Fin.castAdd 2 (Fin.castAdd 1 j)) = WarmReuse.padded p D A j
  rw [Fin.addCases_left, Fin.addCases_left]

theorem padded_retained (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (j : Fin (WholePrefix.tapes p)) (hj : j.val = 52 ∨ j.val = 68) :
    WarmReuse.padded p D A j = A j := by
  have h : Reset.caps p D j = 0 := by simp [Reset.caps, hj]
  simp [WarmReuse.padded, h]

theorem exitTapes_output (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) : exitTapes p D A out (Reuse.output p) = out := by
  simp [exitTapes]

theorem exitTapes_driver (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) : exitTapes p D A out (Reuse.driver p) = List.replicate D true := by
  have h1 : Reuse.driver p ≠ Reuse.output p :=
    slot_ne (by rw [driver_val, output_val]; omega)
  simp [exitTapes, h1]

theorem exitTapes_log (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) : exitTapes p D A out (Reuse.log p) = List.replicate (D + 1) false := by
  have h1 : Reuse.log p ≠ Reuse.output p := slot_ne (by rw [log_val, output_val]; omega)
  have h2 : Reuse.log p ≠ Reuse.driver p := slot_ne (by rw [log_val, driver_val]; omega)
  simp [exitTapes, h1, h2]

theorem exitTapes_native (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) : exitTapes p D A out (Reuse.native p) = A (NativeReadOnly.slot p) := by
  have hT := tapes_ge p
  have h1 : Reuse.native p ≠ Reuse.output p := slot_ne (by rw [native_val, output_val]; omega)
  have h2 : Reuse.native p ≠ Reuse.driver p := slot_ne (by rw [native_val, driver_val]; omega)
  have h3 : Reuse.native p ≠ Reuse.log p := slot_ne (by rw [native_val, log_val]; omega)
  simp [exitTapes, h1, h2, h3]

theorem exitTapes_capacity (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) : exitTapes p D A out (Reuse.capacity p) = A (Retained.capacity p) := by
  have hT := tapes_ge p
  have h1 : Reuse.capacity p ≠ Reuse.output p := slot_ne (by rw [capacity_val, output_val]; omega)
  have h2 : Reuse.capacity p ≠ Reuse.driver p := slot_ne (by rw [capacity_val, driver_val]; omega)
  have h3 : Reuse.capacity p ≠ Reuse.log p := slot_ne (by rw [capacity_val, log_val]; omega)
  have h4 : Reuse.capacity p ≠ Reuse.native p := slot_ne (by rw [capacity_val, native_val]; omega)
  simp [exitTapes, h1, h2, h3, h4]

theorem exitTapes_work (p : Program) (D : ℕ) (A : Fin (WholePrefix.tapes p) → List Bool)
    (out : List Bool) (j : Fin (WholePrefix.tapes p - 2)) :
    exitTapes p D A out (Reuse.work p j) = List.replicate D false := by
  obtain ⟨hb, h52, h68⟩ := Reuse.work_bounds p j
  have h1 : Reuse.work p j ≠ Reuse.output p := slot_ne (by rw [output_val]; omega)
  have h2 : Reuse.work p j ≠ Reuse.driver p := slot_ne (by rw [driver_val]; omega)
  have h3 : Reuse.work p j ≠ Reuse.log p := slot_ne (by rw [log_val]; omega)
  have h4 : Reuse.work p j ≠ Reuse.native p := slot_ne (by rw [native_val]; omega)
  have h5 : Reuse.work p j ≠ Reuse.capacity p := slot_ne (by rw [capacity_val]; omega)
  simp [exitTapes, h1, h2, h3, h4, h5]

/-! ## 3. THE FRAME JOIN — a record-slot-only run as a FULL-configuration `Step`

`WarmActual.run` is stated at `WarmActual.entry`; `Step` is stated at
`⟨machine.start, hin, tin⟩`.  The two are the same configuration, which is the first lemma. -/

theorem entry_control (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) :
    (⟨(WarmActual.machine a).start,
        (WarmActual.entry a row C Q q denominator select out).heads,
        (WarmActual.entry a row C Q q denominator select out).tapes⟩ :
      Configuration (Reuse.tapes (producer a)) _)
      = WarmActual.entry a row C Q q denominator select out :=
  configuration_ext rfl rfl rfl

theorem bank_row_step (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2 ^ Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U * (EquationRow.request row).U),
      Int.ModEq ((2 : ℤ) ^ Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row))
          i.divNat i.modNat) (f i.divNat i.modNat)) :
    Step (WarmActual.machine a) (WarmActual.budget a row C Q)
      (WarmActual.entry a row C Q q denominator select out).heads
      (WarmActual.entry a row C Q q denominator select out).tapes
      (bankHeads (producer a)
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator))
      (exitTapes (producer a) (Driver.value a row.d row.p row.cuts.length C)
        (Warm.input (producer a) row C Q q denominator select)
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)) := by
  obtain ⟨r, hr, _hsteps, hheads, hout, hwork, hdrv, hlog⟩ :=
    WarmActual.run a row C Q q denominator f select out hC hQ hf hc
  have hnat := WarmActual.native_run a (WarmActual.budget a row C Q) _ r hr
  have hcap := WarmActual.capacity_run a (WarmActual.budget a row C Q) _ r hr
  rw [← entry_control a row C Q q denominator select out] at hr
  refine ⟨r, hr, ?_, ?_, runFrom_steps_le _ _ _ _ hr⟩
  · rw [hheads]; rfl
  · funext i
    rcases bank_cover (producer a) i with h | h | h | h | h | ⟨j, h⟩
    · subst h; rw [hout, exitTapes_output]
    · subst h; rw [hdrv, exitTapes_driver]
    · subst h; rw [hlog, exitTapes_log]
    · subst h
      rw [hnat, exitTapes_native]
      show (WarmReuse.entry (producer a) (Warm.machine a)
        (Driver.value a row.d row.p row.cuts.length C)
        (Warm.input (producer a) row C Q q denominator select) out).tapes
          (Reuse.old (producer a) (NativeReadOnly.slot (producer a))) = _
      rw [entry_old, padded_retained]
      exact Or.inl rfl
    · subst h
      rw [hcap, exitTapes_capacity]
      show (WarmReuse.entry (producer a) (Warm.machine a)
        (Driver.value a row.d row.p row.cuts.length C)
        (Warm.input (producer a) row C Q q denominator select) out).tapes
          (Reuse.old (producer a) (Retained.capacity (producer a))) = _
      rw [entry_old, padded_retained]
      exact Or.inr rfl
    · subst h; rw [hwork, exitTapes_work]

theorem hrow_of_step {t st : ℕ} (body : Machine t st)
    (source : ℕ → List Bool → Configuration t st) (emit : ℕ → List Bool) (cost len : ℕ)
    (hstart : ∀ k, k < len → ∀ pre, (source k pre).control = body.start)
    (hstep : ∀ k, k < len → ∀ pre, Step body cost (source k pre).heads (source k pre).tapes
      (source (k + 1) (pre ++ emit k)).heads (source (k + 1) (pre ++ emit k)).tapes)
    (k : ℕ) (hk : k < len) (pre : List Bool) :
    ∃ rc : ExecutionReceipt t st, runFrom body cost (source k pre) = some rc ∧
      rc.final.heads = (source (k + 1) (pre ++ emit k)).heads ∧
      rc.final.tapes = (source (k + 1) (pre ++ emit k)).tapes ∧ rc.steps ≤ cost := by
  obtain ⟨r, hr, hh, ht, hs⟩ := hstep k hk pre
  refine ⟨r, ?_, hh, ht, hs⟩
  have he : (⟨body.start, (source k pre).heads, (source k pre).tapes⟩ : Configuration t st)
      = source k pre := configuration_ext (hstart k hk pre).symm rfl rfl
  rwa [he] at hr

/-- `List.getD` commutes with `List.map` inside the list's own range. -/
theorem getD_map {A B : Type} (g : A → B) (l : List A) (k : ℕ) (d : A) (e : B)
    (hk : k < l.length) : (l.map g).getD k e = g (l.getD k d) := by
  have hk' : k < (l.map g).length := by simpa using hk
  rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk, List.getElem_map]

/-- **The family's `k`-th record word carries the `k`-th pair's `pairValue`** — A.13.9's
\(\sum_{z:\mathbf F(z)=\mathbf f}T_{e,\mathbf f}(z)\)
(`Proof/CaseAnalysis/FinalExternalRowLoop.lean`).  The emit `family_run` demands is therefore a
`Stream.recordWord` of a quantity the paper names, not of a list position. -/
theorem emit_eq_pairWord (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (den : ℕ)
    (dflt : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request) × (Fin request.circuits.length → ℕ))
    (k : ℕ) (hk : k < (wordList liveScale targetDenominator request b est den).length) :
    (wordList liveScale targetDenominator request b est den).getD k []
      = Stream.recordWord b est
          (pairValue liveScale targetDenominator request
            ((pairList liveScale targetDenominator request).getD k dflt).1
            ((pairList liveScale targetDenominator request).getD k dflt).2) den := by
  have hlen : k < (pairList liveScale targetDenominator request).length := by
    simpa [wordList] using hk
  show ((pairList liveScale targetDenominator request).map
    (fun p => pairWord liveScale targetDenominator request b est den p.1 p.2)).getD k [] = _
  rw [getD_map _ _ k dflt _ hlen]
  rfl

theorem bank_row_step_docked (a : WilliamsAlgorithm) {N : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (hinj : Function.Injective slots)
    (H0 : Fin N → ℕ) (A0 : Fin N → List Bool)
    (row : EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2 ^ Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U * (EquationRow.request row).U),
      Int.ModEq ((2 : ℤ) ^ Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row))
          i.divNat i.modNat) (f i.divNat i.modNat)) :
    Step (RecoveryFocus.machine slots (WarmActual.machine a)) (WarmActual.budget a row C Q)
      (dockH slots H0 (WarmActual.entry a row C Q q denominator select out).heads)
      (install slots A0 (WarmActual.entry a row C Q q denominator select out).tapes)
      (dockH slots H0 (bankHeads (producer a)
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)))
      (install slots A0 (exitTapes (producer a)
        (Driver.value a row.d row.p row.cuts.length C)
        (Warm.input (producer a) row C Q q denominator select)
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator))) :=
  (bank_row_step a row C Q q denominator f select out hC hQ hf hc).focus slots hinj H0 A0

/-- The round body: the docked estimator bank, then the inter-row re-lay. -/
noncomputable def roundBody (a : WilliamsAlgorithm) {N sr : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (reload : Machine N sr) :=
  Composition.machine (RecoveryFocus.machine slots (WarmActual.machine a)) reload

/-- The round's entry configuration: the bank laid for round `k`'s printed row inside the ambient,
with the accumulated record stream `out` on the accumulator slot, at the composed body's start
control.  Everything outside the bank's slot image is the caller's own `H0`/`A0`. -/
noncomputable def roundSource (a : WilliamsAlgorithm) {N sr : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (reload : Machine N sr)
    (H0 : Fin N → ℕ) (A0 : Fin N → List Bool)
    (row : ℕ → EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → Bool)
    (k : ℕ) (out : List Bool) :=
  Configuration.mk (roundBody a slots reload).start
    (dockH slots H0 (WarmActual.entry a (row k) C Q q den (select k) out).heads)
    (install slots A0 (WarmActual.entry a (row k) C Q q den (select k) out).tapes)

theorem roundSource_slot (a : WilliamsAlgorithm) {N sr : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (hinj : Function.Injective slots)
    (reload : Machine N sr) (H0 : Fin N → ℕ) (A0 : Fin N → List Bool)
    (row : ℕ → EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → Bool)
    (k : ℕ) (out : List Bool) :
    (roundSource a slots reload H0 A0 row C Q q den select k out).tapes
        (slots (Reuse.output (producer a))) = out := by
  show install slots A0 (WarmActual.entry a (row k) C Q q den (select k) out).tapes
    (slots (Reuse.output (producer a))) = out
  rw [install_slot slots hinj]
  exact entry_output (producer a) (Warm.machine a)
    (Driver.value a (row k).d (row k).p (row k).cuts.length C)
    (Warm.input (producer a) (row k) C Q q den (select k)) out

/-- **The reloader must not move a head.**  The frame join already exits at exactly the head
function the next round's entry wants, so `hreload`'s head obligation is an identity.  (Named
`roundSource_heads`, not `reload_heads`: `C10InterRowReloader.reload_heads`
(`Proof/CaseAnalysis/FinalInterRowReloader.lean`) is a different statement about the reloader's
own slot map, and this module must not shadow it.) -/
theorem roundSource_heads (a : WilliamsAlgorithm) {N sr : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (reload : Machine N sr)
    (H0 : Fin N → ℕ) (A0 : Fin N → List Bool)
    (row : ℕ → EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → Bool)
    (k : ℕ) (X : List Bool) :
    (roundSource a slots reload H0 A0 row C Q q den select k X).heads
      = dockH slots H0 (bankHeads (producer a) X) :=
  congrArg (dockH slots H0)
    (entry_heads (producer a) (Warm.machine a)
      (Driver.value a (row k).d (row k).p (row k).cuts.length C)
      (Warm.input (producer a) (row k) C Q q den (select k)) X)

theorem bank_family_run (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (a : WilliamsAlgorithm) {N sr : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (hinj : Function.Injective slots)
    (reload : Machine N sr) (H0 : Fin N → ℕ) (A0 : Fin N → List Bool)
    (row : ℕ → EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (den : ℕ)
    (tab : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → ℕ)
    (select : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → Bool)
    (rowCost reloadCost b : ℕ) (est : CompetitorValidity.Estimate) (out : List Bool)
    (hC : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → (Header.stream (row k)).length ≤ C)
    (hQ : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → Q ≤ (EquationRow.request (row k)).p)
    (hf : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → ∀ i j, tab k i j < 2 ^ Q)
    (hc : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → ∀ i : Fin ((EquationRow.request (row k)).U * (EquationRow.request (row k)).U),
        Int.ModEq ((2 : ℤ) ^ Q)
          (SupplierPrinter.weightedDominance (leftScore (EquationRow.request (row k)))
            (rightScore (EquationRow.request (row k))) (weight (EquationRow.request (row k)))
            i.divNat i.modNat) (tab k i.divNat i.modNat))
    (hbudget : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → WarmActual.budget a (row k) C Q ≤ rowCost)
    (hemit : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → Stream.recordWord (scalarWidth (EquationRow.request (row k)) Q) q
          (selected (CompetitorSelectedCells.cells (row k).odd (tab k) (select k))).sum den
        = (wordList liveScale targetDenominator request b est den).getD k [])
    (hreload : ∀ k, k < (wordList liveScale targetDenominator request b est den).length
      → ∀ X : List Bool,
        Step reload reloadCost (dockH slots H0 (bankHeads (producer a) X))
          (install slots A0
            (exitTapes (producer a) (Driver.value a (row k).d (row k).p (row k).cuts.length C)
              (Warm.input (producer a) (row k) C Q q den (select k)) X))
          (roundSource a slots reload H0 A0 row C Q q den select (k + 1) X).heads
          (roundSource a slots reload H0 A0 row C Q q den select (k + 1) X).tapes) :
    ∃ T, Step (familyWriter (roundBody a slots reload))
        (familyFuel (wordList liveScale targetDenominator request b est den).length
          (rowCost + 1 + reloadCost))
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0
          (roundSource a slots reload H0 A0 row C Q q den select 0 out)
          (wordList liveScale targetDenominator request b est den).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0
          (roundSource a slots reload H0 A0 row C Q q den select 0 out)
          (wordList liveScale targetDenominator request b est den).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (roundSource a slots reload H0 A0 row C Q q den select
            (wordList liveScale targetDenominator request b est den).length
            (out ++ familyStream liveScale targetDenominator request b est den))
          (wordList liveScale targetDenominator request b est den).length 1).heads
        T ∧
      T ((slots (Reuse.output (producer a))).castAdd 1) =
        out ++ familyStream liveScale targetDenominator request b est den ∧
      (((pairList liveScale targetDenominator request).map
          (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum) =
        ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
          request).acceptanceCount := by
  refine family_run spectrum liveScale targetDenominator request
    (roundBody a slots reload) (roundSource a slots reload H0 A0 row C Q q den select)
    (slots (Reuse.output (producer a))) (rowCost + 1 + reloadCost) b est den out
    (fun k pre => roundSource_slot a slots hinj reload H0 A0 row C Q q den select k pre)
    (fun k _ pre => rfl) (fun k hk pre => ?_)
  refine hrow_of_step (roundBody a slots reload)
    (roundSource a slots reload H0 A0 row C Q q den select)
    (fun j => (wordList liveScale targetDenominator request b est den).getD j [])
    (rowCost + 1 + reloadCost)
    (wordList liveScale targetDenominator request b est den).length
    (fun _ _ _ => rfl) (fun j hj X => ?_) k hk pre
  have hbank := bank_row_step_docked a slots hinj H0 A0 (row j) C Q q den (tab j) (select j) X
    (hC j hj) (hQ j hj) (hf j hj) (hc j hj)
  have hseq := Step.seq hbank (hreload j hj
    (X ++ Stream.recordWord (scalarWidth (EquationRow.request (row j)) Q) q
      (selected (CompetitorSelectedCells.cells (row j).odd (tab j) (select j))).sum den))
  rw [hemit j hj] at hseq
  exact hseq.enlarge (by have := hbudget j hj; omega)

/-- **`hgrow` at consecutive rounds**, for a per-round row function that agrees with the re-ordered
enumeration.  This is what makes `hreload` satisfiable: `C10NativeReload.reload_native_step`
(`Proof/CaseAnalysis/FinalNativeReload.lean`) asks for exactly this inequality, and
`C10NativeReload.native_growth_necessary` (`:154`) proves no construction avoids it. -/
theorem ordered_growth (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (key : Round liveScale targetDenominator request → EquationRow.Input)
    (row : ℕ → EquationRow.Input)
    (hkey : ∀ k, ∀ hk : k < (orderedPairList liveScale targetDenominator request key).length,
      row k = orderedRow liveScale targetDenominator request key k hk)
    (k : ℕ) (hk : k + 1 < (orderedPairList liveScale targetDenominator request key).length) :
    (Header.stream (row k)).length ≤ (Header.stream (row (k + 1))).length := by
  rw [hkey k (Nat.lt_of_succ_lt hk), hkey (k + 1) hk]
  exact orderedPairList_growth liveScale targetDenominator request key k hk

theorem ordered_bank_family_run (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (key : Round liveScale targetDenominator request → EquationRow.Input)
    (a : WilliamsAlgorithm) {N sr : ℕ}
    (slots : Fin (Reuse.tapes (producer a)) → Fin N) (hinj : Function.Injective slots)
    (reload : Machine N sr) (H0 : Fin N → ℕ) (A0 : Fin N → List Bool)
    (row : ℕ → EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (den : ℕ)
    (tab : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → ℕ)
    (select : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → Bool)
    (rowCost reloadCost b : ℕ) (est : CompetitorValidity.Estimate) (out : List Bool)
    (hC : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → (Header.stream (row k)).length ≤ C)
    (hQ : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → Q ≤ (EquationRow.request (row k)).p)
    (hf : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → ∀ i j, tab k i j < 2 ^ Q)
    (hc : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → ∀ i : Fin ((EquationRow.request (row k)).U * (EquationRow.request (row k)).U),
        Int.ModEq ((2 : ℤ) ^ Q)
          (SupplierPrinter.weightedDominance (leftScore (EquationRow.request (row k)))
            (rightScore (EquationRow.request (row k))) (weight (EquationRow.request (row k)))
            i.divNat i.modNat) (tab k i.divNat i.modNat))
    (hbudget : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → WarmActual.budget a (row k) C Q ≤ rowCost)
    (hemit : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → Stream.recordWord (scalarWidth (EquationRow.request (row k)) Q) q
          (selected (CompetitorSelectedCells.cells (row k).odd (tab k) (select k))).sum den
        = (orderedWordList liveScale targetDenominator request key b est den).getD k [])
    (hreload : ∀ k, k < (orderedWordList liveScale targetDenominator request key b est den).length
      → ∀ X : List Bool,
        Step reload reloadCost (dockH slots H0 (bankHeads (producer a) X))
          (install slots A0
            (exitTapes (producer a) (Driver.value a (row k).d (row k).p (row k).cuts.length C)
              (Warm.input (producer a) (row k) C Q q den (select k)) X))
          (roundSource a slots reload H0 A0 row C Q q den select (k + 1) X).heads
          (roundSource a slots reload H0 A0 row C Q q den select (k + 1) X).tapes) :
    ∃ T, Step (familyWriter (roundBody a slots reload))
        (familyFuel (orderedWordList liveScale targetDenominator request key b est den).length
          (rowCost + 1 + reloadCost))
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0
          (roundSource a slots reload H0 A0 row C Q q den select 0 out)
          (orderedWordList liveScale targetDenominator request key b est den).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0
          (roundSource a slots reload H0 A0 row C Q q den select 0 out)
          (orderedWordList liveScale targetDenominator request key b est den).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (roundSource a slots reload H0 A0 row C Q q den select
            (orderedWordList liveScale targetDenominator request key b est den).length
            (out ++ orderedFamilyStream liveScale targetDenominator request key b est den))
          (orderedWordList liveScale targetDenominator request key b est den).length 1).heads
        T ∧
      T ((slots (Reuse.output (producer a))).castAdd 1) =
        out ++ orderedFamilyStream liveScale targetDenominator request key b est den ∧
      (((orderedPairList liveScale targetDenominator request key).map
          (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum) =
        ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
          request).acceptanceCount := by
  refine ordered_family_run liveScale targetDenominator request spectrum key
    (roundBody a slots reload) (roundSource a slots reload H0 A0 row C Q q den select)
    (slots (Reuse.output (producer a))) (rowCost + 1 + reloadCost) b est den out
    (fun k pre => roundSource_slot a slots hinj reload H0 A0 row C Q q den select k pre)
    (fun k _ pre => rfl) (fun k hk pre => ?_)
  refine hrow_of_step (roundBody a slots reload)
    (roundSource a slots reload H0 A0 row C Q q den select)
    (fun j => (orderedWordList liveScale targetDenominator request key b est den).getD j [])
    (rowCost + 1 + reloadCost)
    (orderedWordList liveScale targetDenominator request key b est den).length
    (fun _ _ _ => rfl) (fun j hj X => ?_) k hk pre
  have hbank := bank_row_step_docked a slots hinj H0 A0 (row j) C Q q den (tab j) (select j) X
    (hC j hj) (hQ j hj) (hf j hj) (hc j hj)
  have hseq := Step.seq hbank (hreload j hj
    (X ++ Stream.recordWord (scalarWidth (EquationRow.request (row j)) Q) q
      (selected (CompetitorSelectedCells.cells (row j).odd (tab j) (select j))).sum den))
  rw [hemit j hj] at hseq
  exact hseq.enlarge (by have := hbudget j hj; omega)

/-- **`hemit` reduced to `selected_sum_printer`.**  The three residual facts are: the scheduled
record width is uniform across the printed family, the estimate is the family's own, and round
`k`'s SELECTED cell sum is the `k`-th pair's `pairValue` -- which
`C10ExternalRowLoop.selected_sum_printer` (`Proof/CaseAnalysis/FinalExternalRowLoop.lean`)
supplies at each printed pair.  Nothing about the RECORD SHAPE enters: the frame join is
denominator- and record-shape-agnostic. -/
theorem emit_of_payload (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (den : ℕ)
    (dflt : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request) × (Fin request.circuits.length → ℕ))
    (row : ℕ → EquationRow.Input) (Q : ℕ) (q : CompetitorValidity.Estimate)
    (tab : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → ℕ)
    (select : (k : ℕ) → Fin (EquationRow.request (row k)).U →
      Fin (EquationRow.request (row k)).U → Bool)
    (k : ℕ) (hk : k < (wordList liveScale targetDenominator request b est den).length)
    (hb : scalarWidth (EquationRow.request (row k)) Q = b) (hq : q = est)
    (hsum : (selected (CompetitorSelectedCells.cells (row k).odd (tab k) (select k))).sum
      = pairValue liveScale targetDenominator request
          ((pairList liveScale targetDenominator request).getD k dflt).1
          ((pairList liveScale targetDenominator request).getD k dflt).2) :
    Stream.recordWord (scalarWidth (EquationRow.request (row k)) Q) q
        (selected (CompetitorSelectedCells.cells (row k).odd (tab k) (select k))).sum den
      = (wordList liveScale targetDenominator request b est den).getD k [] := by
  rw [hb, hq, hsum, emit_eq_pairWord liveScale targetDenominator request b est den dflt k hk]

/-! ## 6. The resource statement — bucket ANALYSIS CALLS

`paper.tex:1409-1412` charges the analysis calls "and their remaining polynomial overhead" at
\(q^{p_{\mathrm{call},c}}\) times one residual cell, displayed at `paper.tex:1437-1439` and
aggregated at `paper.tex:1424-1425`.  `CloseoutFinalC10RoundBudget.WidthPoly`
(`Proof/CaseAnalysis/FinalRoundBudget.lean`) is that predicate and
`CloseoutFinalC10RoundBudget.WidthPoly.le_hotFuel` (`:254`) is its absorption into the cell
`hotFuel` (`Proof/CaseAnalysis/FinalCostAtTable.lean`).  This section composes with
those rather than redoing them; every quantity below is `k`-free (`k` occurs only as the width
index of `widthPower`, never inside a fuel).

**One observation for the consumer, because it changes what `roundFuel` has to be.**
`CloseoutFinalC10RoundBudget.roundFuel` (`Proof/CaseAnalysis/FinalRoundBudget.lean`) is
`clearedFuel decode + 1 + terms * (clearedFuel (termFuel w rows shift) + 1) + 1 + clearedFuel
cursor`, and its `rowAnswerFuel w rows` charges the SUMMATION over `rows` already-printed record
words -- it has no term for the family loop that PRINTS them.  `familyFuel_at_cell` is therefore an
ADDITION to that ledger, not a re-derivation of it; `WidthPoly.add`
(`Proof/CaseAnalysis/FinalRoundBudget.lean`) makes the addition free, because the absorption is
asymptotic and so insensitive to the constant.  **No band clear is added here**: the clear of this
segment is already inside `Reuse.budget` (`Proof/CaseAnalysis/RowsEstimatorReuseRun.lean`), whose
`afterBudget b D = 2*D + 40*b + 61` (`Proof/CaseAnalysis/RowsEstimatorReuseAfter.lean`) IS
`Reuse.after` = append-then-erase.  Charging `clearedFuel` again here would double-count. -/

theorem widthPoly_of_widthPower (sources : RepairSource.EightSources) (k c : ℕ) (rows : ℕ → ℕ)
    (hrows : ∀ N, rows N ≤ widthPower sources k c N) :
    CloseoutFinalC10RoundBudget.WidthPoly sources k rows :=
  ⟨1, c, fun N => by simpa using hrows N⟩

theorem widthPoly_familyFuel (sources : RepairSource.EightSources) (k : ℕ) (rows cost : ℕ → ℕ)
    (hrows : CloseoutFinalC10RoundBudget.WidthPoly sources k rows)
    (hcost : CloseoutFinalC10RoundBudget.WidthPoly sources k cost) :
    CloseoutFinalC10RoundBudget.WidthPoly sources k
      (fun N => familyFuel (rows N) (cost N)) :=
  (hrows.mul (hcost.add (CloseoutFinalC10RoundBudget.WidthPoly.const sources k 3))).add
    (CloseoutFinalC10RoundBudget.WidthPoly.const sources k 3)

/-- **The family loop fits ONE analysis-call cell.**  `hotFuel` is the paper's
\(2^q/q^\sigma\) (`paper.tex:3555-3557`), which is the `cost` `partsOfHotCost` pins and
`callsReady_of_rounds` consumes.  The per-round re-lay enters through `cost`; whether IT is
`q^{O(1)}` is `paper.tex:2290-2296`'s question, and that sentence answers it at `2^{o(q)}` rather
than at `q^{O(1)}` -- a route no compiled statement provides, so it is a hypothesis here. -/
theorem familyFuel_at_cell (sources : RepairSource.EightSources) (k r degree : ℕ)
    (rows cost : ℕ → ℕ)
    (hrows : CloseoutFinalC10RoundBudget.WidthPoly sources k rows)
    (hcost : CloseoutFinalC10RoundBudget.WidthPoly sources k cost) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      familyFuel (rows N) (cost N)
        ≤ hotFuel sources k r degree N :=
  (widthPoly_familyFuel sources k rows cost hrows hcost).le_hotFuel r degree

end NearCubicWires.RepairOrdinary.C10RowFrameJoin

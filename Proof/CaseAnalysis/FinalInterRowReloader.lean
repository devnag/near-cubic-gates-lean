import Proof.CaseAnalysis.RowsEstimatorActual
import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmRetained
import Proof.CaseAnalysis.RowsEstimatorPrepareCopy
import Proof.MachineModel.Runs

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

namespace NearCubicWires.RepairSource.CloseoutFinal.C10InterRowReloader

/-! ## 1. The reloader's tape space: the reusable bank plus one retained port per work slot -/

/-- The reloader's tapes: `Reuse.tapes p` (the reusable estimator bank, its growing output stream,
its paid driver word and its rewind log) followed by one retained source port per work slot. -/
def tapes (p : Program) : ℕ := Reuse.tapes p + (WholePrefix.tapes p - 2)

/-- The reusable bank, embedded unchanged. -/
def bank (p : Program) (i : Fin (Reuse.tapes p)) : Fin (tapes p) :=
  i.castAdd (WholePrefix.tapes p - 2)

/-- One retained source port per work slot: these carry the next row's words. -/
def port (p : Program) (i : Fin (WholePrefix.tapes p - 2)) : Fin (tapes p) :=
  i.natAdd (Reuse.tapes p)

theorem bank_val (p : Program) (i : Fin (Reuse.tapes p)) : (bank p i).val = i.val := rfl

theorem port_val (p : Program) (i : Fin (WholePrefix.tapes p - 2)) :
    (port p i).val = Reuse.tapes p + i.val := rfl

theorem reuse_tapes_val (p : Program) : Reuse.tapes p = WholePrefix.tapes p + 1 + 2 := rfl

theorem driver_val (p : Program) : (Reuse.driver p).val = WholePrefix.tapes p + 2 := rfl

theorem log_val (p : Program) : (Reuse.log p).val = WholePrefix.tapes p := rfl

theorem native_val (p : Program) : (Reuse.native p).val = 52 := rfl

theorem prefix_wide (p : Program) : (70 : ℕ) ≤ WholePrefix.tapes p := by
  unfold WholePrefix.tapes
  omega

/-- The reloader's slot map: the retained ports, then the reusable bank's own erase slots (its work
tapes, its driver word and its rewind log) in `MetadataBatch`'s tape order. -/
def slots (p : Program) :
    Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1) → Fin (tapes p) :=
  Fin.addCases (m := WholePrefix.tapes p - 2) (n := WholePrefix.tapes p - 2 + 1 + 1)
    (port p) (fun j => bank p (Reuse.eraseSlots p j))

theorem at_port (p : Program) (i : Fin (WholePrefix.tapes p - 2)) :
    slots p ((i.castAdd ((WholePrefix.tapes p - 2) + 1)).castAdd 1) = port p i := by
  have he : ((i.castAdd ((WholePrefix.tapes p - 2) + 1)).castAdd 1 :
      Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1)) =
      i.castAdd (WholePrefix.tapes p - 2 + 1 + 1) :=
    Fin.ext (by simp only [Fin.val_castAdd])
  rw [he]
  simp only [slots, Fin.addCases_left]

theorem at_work (p : Program) (i : Fin (WholePrefix.tapes p - 2)) :
    slots p (((i.castAdd 1).natAdd (WholePrefix.tapes p - 2)).castAdd 1) =
      bank p (Reuse.work p i) := by
  have he : ((((i.castAdd 1).natAdd (WholePrefix.tapes p - 2)).castAdd 1) :
      Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1)) =
      Fin.natAdd (WholePrefix.tapes p - 2) ((i.castAdd 1).castAdd 1) :=
    Fin.ext (by simp only [Fin.val_castAdd, Fin.val_natAdd])
  rw [he]
  simp only [slots, Fin.addCases_right, Reuse.erase_work]

theorem at_driver (p : Program) (i : Fin 1) :
    slots p (((i.natAdd (WholePrefix.tapes p - 2)).natAdd (WholePrefix.tapes p - 2)).castAdd 1) =
      bank p (Reuse.driver p) := by
  have he : ((((i.natAdd (WholePrefix.tapes p - 2)).natAdd (WholePrefix.tapes p - 2)).castAdd 1) :
      Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1)) =
      Fin.natAdd (WholePrefix.tapes p - 2)
        ((i.natAdd (WholePrefix.tapes p - 2)).castAdd 1) :=
    Fin.ext (by simp only [Fin.val_castAdd, Fin.val_natAdd])
  rw [he]
  simp only [slots, Fin.addCases_right, Reuse.eraseSlots, Fin.addCases_left, Fin.addCases_right]

theorem at_log (p : Program) (i : Fin 1) :
    slots p (i.natAdd ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1))) =
      bank p (Reuse.log p) := by
  have he : ((i.natAdd ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1))) :
      Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1)) =
      Fin.natAdd (WholePrefix.tapes p - 2) (i.natAdd (WholePrefix.tapes p - 2 + 1)) :=
    Fin.ext (by simp only [Fin.val_natAdd]; omega)
  rw [he]
  simp only [slots, Fin.addCases_right, Reuse.eraseSlots, Fin.addCases_right]

theorem port_injective (p : Program) : Function.Injective (port p) := by
  intro i j he
  have hv := congrArg (fun z : Fin (tapes p) => z.val) he
  simp only [port_val] at hv
  exact Fin.ext (by omega)

theorem slots_injective (p : Program) : Function.Injective (slots p) := by
  intro i j
  refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := WholePrefix.tapes p - 2 + 1 + 1)
      (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := WholePrefix.tapes p - 2 + 1 + 1)
      (fun b => ?_) (fun b => ?_) j
  · intro he
    simp only [slots, Fin.addCases_left] at he
    exact congrArg (fun z => Fin.castAdd (WholePrefix.tapes p - 2 + 1 + 1) z) (port_injective p he)
  · intro he
    simp only [slots, Fin.addCases_left, Fin.addCases_right] at he
    have hv := congrArg (fun z : Fin (tapes p) => z.val) he
    simp only [port_val, bank_val] at hv
    have hb := (Reuse.eraseSlots p b).isLt
    omega
  · intro he
    simp only [slots, Fin.addCases_left, Fin.addCases_right] at he
    have hv := congrArg (fun z : Fin (tapes p) => z.val) he
    simp only [port_val, bank_val] at hv
    have hb := (Reuse.eraseSlots p a).isLt
    omega
  · intro he
    simp only [slots, Fin.addCases_right] at he
    have hv := congrArg (fun z : Fin (tapes p) => z.val) he
    simp only [bank_val] at hv
    exact congrArg (fun z => Fin.natAdd (WholePrefix.tapes p - 2) z)
      (Reuse.erase_injective p (Fin.ext hv))

/-! ## 2. The words the reloader lays: round `k+1`'s own estimator input, slot by slot -/

/-- The `WholePrefix` index of a reusable work slot. -/
def rowIndex (p : Program) (i : Fin (WholePrefix.tapes p - 2)) : Fin (WholePrefix.tapes p) :=
  ⟨(Reuse.work p i).val, (Reuse.work_bounds p i).1⟩

theorem work_eq_old (p : Program) (i : Fin (WholePrefix.tapes p - 2)) :
    Reuse.work p i = Reuse.old p (rowIndex p i) := Fin.ext rfl

theorem caps_row (p : Program) (D : ℕ) (i : Fin (WholePrefix.tapes p - 2)) :
    Reset.caps p D (rowIndex p i) = D := by
  have h := Reuse.work_bounds p i
  unfold Reset.caps
  refine if_neg ?_
  change ¬((Reuse.work p i).val = 52 ∨ (Reuse.work p i).val = 68)
  tauto

/-- **The reload data**: the next row's estimator input, restricted to the reusable work slots.
`Warm.input` (`Proof/CaseAnalysis/CloseoutRowsEstimatorWarm.lean`) is the literal caller bank of the row —
by `WarmFields.installed` (`Proof/CaseAnalysis/RowsEstimatorSparse.lean`) it is
`WarmFields.bare` with the seven metadata words installed. -/
noncomputable def rowData (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (i : Fin (WholePrefix.tapes p - 2)) : List Bool :=
  Warm.input p row C Q q denominator select (rowIndex p i)

/-- Every reload word fits the paid capacity: `InputSupport.warm`
(`Proof/CaseAnalysis/RowsEstimatorInputSupport.lean`). -/
theorem rowData_fit (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (i : Fin (WholePrefix.tapes (CompetitorCrossScheduler.producer a) - 2)) :
    (rowData (CompetitorCrossScheduler.producer a) row C Q q denominator select i).length ≤
      Driver.value a row.d row.p row.cuts.length C :=
  InputSupport.warm a row C Q q denominator select hC hQ _

/-! ## 3. The consumer's target: what round `k+1`'s entry configuration holds -/

/-- Round `k+1`'s entry (`WarmReuse.entry`, `Proof/CaseAnalysis/RowsEstimatorReuse.lean`) carries
the padded estimator input on the old bank. -/
theorem entry_old {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s) (D : ℕ)
    (A : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool)
    (j : Fin (WholePrefix.tapes p)) :
    (WarmReuse.entry p worker D A out).tapes (Reuse.old p j) = WarmReuse.padded p D A j := by
  simp only [WarmReuse.entry, Composition.leftConfig, TapeEmbedding.config, initialConfiguration,
    Reuse.old, Fin.addCases_left]

/-- **The reload target, in the consumer's own vocabulary.**  Round `k+1`'s entry carries
`ZeroPadding.pad D (rowData …)` on every `Reuse.work` slot. -/
theorem entry_work {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (row : EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (D : ℕ) (out : List Bool) (i : Fin (WholePrefix.tapes p - 2)) :
    (WarmReuse.entry p worker D (Warm.input p row C Q q denominator select) out).tapes
        (Reuse.work p i) =
      ZeroPadding.pad D (rowData p row C Q q denominator select i) := by
  rw [work_eq_old, entry_old]
  simp only [WarmReuse.padded, caps_row, rowData]

/-! ## 4. The reloader: one docked `MetadataBatch` pass -/

/-- **The reloader.**  One `CloseoutRowsEstimator.MetadataBatch.machine` pass
(`Proof/CaseAnalysis/RowsEstimatorMetadataBatch.lean`) docked at the retained ports and the reusable
work slots. -/
noncomputable def machine (p : Program) :=
  RecoveryFocus.machine (slots p) (MetadataBatch.machine (WholePrefix.tapes p - 2))

theorem reload_input (p : Program) (data : Fin (WholePrefix.tapes p - 2) → List Bool) (D : ℕ)
    (A : Fin (tapes p) → List Bool)
    (hport : ∀ i, A (port p i) = data i)
    (hwork : ∀ i, A (bank p (Reuse.work p i)) = List.replicate D false)
    (hdriver : A (bank p (Reuse.driver p)) = List.replicate D true)
    (hlog : A (bank p (Reuse.log p)) = List.replicate (D + 1) false)
    (j : Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1)) :
    A (slots p j) = MetadataBatch.input data D j := by
  refine Fin.addCases (m := (WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1)) (n := 1)
    (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := (WholePrefix.tapes p - 2) + 1)
      (fun l => ?_) (fun l => ?_) k
    · simpa only [at_port, MetadataBatch.input, Fin.addCases_left] using hport l
    · refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := 1) (fun m => ?_) (fun m => ?_) l
      · simpa only [at_work, MetadataBatch.input, Fin.addCases_left, Fin.addCases_right] using hwork m
      · simpa only [at_driver, MetadataBatch.input, Fin.addCases_left, Fin.addCases_right]
          using hdriver
  · simpa only [at_log, MetadataBatch.input, Fin.addCases_right] using hlog

theorem reload_heads (p : Program) (H : Fin (tapes p) → ℕ)
    (hport : ∀ i, H (port p i) = 0)
    (hwork : ∀ i, H (bank p (Reuse.work p i)) = 0)
    (hdriver : H (bank p (Reuse.driver p)) = 0)
    (hlog : H (bank p (Reuse.log p)) = 0)
    (j : Fin ((WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1) + 1)) :
    H (slots p j) = 0 := by
  refine Fin.addCases (m := (WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1)) (n := 1)
    (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := (WholePrefix.tapes p - 2) + 1)
      (fun l => ?_) (fun l => ?_) k
    · simpa only [at_port] using hport l
    · refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := 1) (fun m => ?_) (fun m => ?_) l
      · simpa only [at_work] using hwork m
      · simpa only [at_driver] using hdriver
  · simpa only [at_log] using hlog

theorem reload_step (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (D : ℕ) (H : Fin (tapes p) → ℕ) (A : Fin (tapes p) → List Bool)
    (hfit : ∀ i, (rowData p row C Q q denominator select i).length ≤ D)
    (hph : ∀ i, H (port p i) = 0) (hwh : ∀ i, H (bank p (Reuse.work p i)) = 0)
    (hdh : H (bank p (Reuse.driver p)) = 0) (hlh : H (bank p (Reuse.log p)) = 0)
    (hport : ∀ i, A (port p i) = rowData p row C Q q denominator select i)
    (hwork : ∀ i, A (bank p (Reuse.work p i)) = List.replicate D false)
    (hdriver : A (bank p (Reuse.driver p)) = List.replicate D true)
    (hlog : A (bank p (Reuse.log p)) = List.replicate (D + 1) false) :
    ∃ B, Step (machine p) (2 * D + 4) H A H B ∧
      (∀ i, B (bank p (Reuse.work p i)) =
        WarmReuse.padded p D (Warm.input p row C Q q denominator select) (rowIndex p i)) ∧
      B (bank p (Reuse.driver p)) = List.replicate D true ∧
      B (bank p (Reuse.log p)) = List.replicate (D + 1) false ∧
      (∀ i, B (port p i) = rowData p row C Q q denominator select i) ∧
      (∀ i, (∀ j, slots p j ≠ i) → B i = A i) := by
  obtain ⟨r, hr, hh, ht, hs⟩ :=
    (MetadataBatch.ready (rowData p row C Q q denominator select) D hfit).focus_at
      (slots p) (slots_injective p) H A
      (reload_input p (rowData p row C Q q denominator select) D A hport hwork hdriver hlog)
      (reload_heads p H hph hwh hdh hlh)
  refine ⟨install (slots p) A (MetadataBatch.output (rowData p row C Q q denominator select) D),
    ⟨r, hr, hh, ht, hs.le⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← at_work p i, install_slot _ (slots_injective p)]
    simp only [MetadataBatch.output, Fin.addCases_left, Fin.addCases_right, WarmReuse.padded,
      caps_row, rowData]
  · rw [← at_driver p 0, install_slot _ (slots_injective p)]
    simp only [MetadataBatch.output, Fin.addCases_left, Fin.addCases_right]
  · rw [← at_log p 0, install_slot _ (slots_injective p)]
    simp only [MetadataBatch.output, Fin.addCases_right]
  · intro i
    rw [← at_port p i, install_slot _ (slots_injective p)]
    simp only [MetadataBatch.output, Fin.addCases_left]
  · intro i hi
    exact install_other _ _ _ _ hi

/-- **The same conclusion in the consumer's vocabulary.**  After `reload_step` the bank carries
round `k+1`'s entry configuration (`WarmReuse.entry`) on every `Reuse.work` slot. -/
theorem reload_entry {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (row : EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (D : ℕ) (out : List Bool) (H : Fin (tapes p) → ℕ) (A : Fin (tapes p) → List Bool)
    (hfit : ∀ i, (rowData p row C Q q denominator select i).length ≤ D)
    (hph : ∀ i, H (port p i) = 0) (hwh : ∀ i, H (bank p (Reuse.work p i)) = 0)
    (hdh : H (bank p (Reuse.driver p)) = 0) (hlh : H (bank p (Reuse.log p)) = 0)
    (hport : ∀ i, A (port p i) = rowData p row C Q q denominator select i)
    (hwork : ∀ i, A (bank p (Reuse.work p i)) = List.replicate D false)
    (hdriver : A (bank p (Reuse.driver p)) = List.replicate D true)
    (hlog : A (bank p (Reuse.log p)) = List.replicate (D + 1) false) :
    ∃ B, Step (machine p) (2 * D + 4) H A H B ∧
      (∀ i, B (bank p (Reuse.work p i)) =
        (WarmReuse.entry p worker D (Warm.input p row C Q q denominator select) out).tapes
          (Reuse.work p i)) := by
  obtain ⟨B, hstep, hw, _, _, _, _⟩ := reload_step p row C Q q denominator select D H A hfit
    hph hwh hdh hlh hport hwork hdriver hlog
  refine ⟨B, hstep, fun i => ?_⟩
  rw [hw i, entry_work p worker row C Q q denominator select D out i]
  simp only [WarmReuse.padded, caps_row, rowData]

/-! ## 5. The residue: the one externally owned tape the reloader cannot reach -/

/-- `Reuse.native` (`Proof/CaseAnalysis/RowsEstimatorReuseLayout.lean`) is outside `Reuse.work`'s image
(`Reuse.work_bounds`, `Proof/CaseAnalysis/RowsEstimatorReuseLayout.lean`). -/
theorem native_not_work (p : Program) (i : Fin (WholePrefix.tapes p - 2)) :
    Reuse.work p i ≠ Reuse.native p := by
  intro he
  have hv := congrArg (fun z : Fin (Reuse.tapes p) => z.val) he
  simp only [native_val] at hv
  exact (Reuse.work_bounds p i).2.1 hv

/-- The reloader's slot map never names the externally owned native tape, so `reload_step` leaves it
untouched. -/
theorem reload_avoids_native (p : Program) : ∀ j, slots p j ≠ bank p (Reuse.native p) := by
  have hn := prefix_wide p
  have ht := reuse_tapes_val p
  intro j
  refine Fin.addCases (m := (WholePrefix.tapes p - 2) + ((WholePrefix.tapes p - 2) + 1)) (n := 1)
    (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := (WholePrefix.tapes p - 2) + 1)
      (fun l => ?_) (fun l => ?_) k
    · intro he
      rw [at_port] at he
      have hv := congrArg (fun z : Fin (tapes p) => z.val) he
      simp only [port_val, bank_val, native_val] at hv
      omega
    · refine Fin.addCases (m := WholePrefix.tapes p - 2) (n := 1) (fun m => ?_) (fun m => ?_) l
      · intro he
        rw [at_work] at he
        exact native_not_work p m (Fin.ext (congrArg (fun z : Fin (tapes p) => z.val) he))
      · intro he
        rw [at_driver] at he
        have hv := congrArg (fun z : Fin (tapes p) => z.val) he
        simp only [bank_val, driver_val, native_val] at hv
        omega
  · intro he
    rw [at_log] at he
    have hv := congrArg (fun z : Fin (tapes p) => z.val) he
    simp only [bank_val, log_val, native_val] at hv
    omega

/-- **What round `k+1`'s entry needs on the externally owned native tape**: the NEXT row's printed
cut stream `CloseoutRowsEstimator.Header.stream` (`Proof/CaseAnalysis/RowsEstimatorHeader.lean`). -/
theorem entry_native {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s)
    (row : EquationRow.Input) (C Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (D : ℕ) (out : List Bool) :
    (WarmReuse.entry p worker D (Warm.input p row C Q q denominator select) out).tapes
        (Reuse.native p) = Header.stream row := by
  have hnat : Reuse.native p =
      Reuse.old p ((52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p)) := rfl
  have hval : (((52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p)) :
      Fin (WholePrefix.tapes p)).val = 52 := rfl
  have hcap : Reset.caps p D ((52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p)) = 0 := by
    unfold Reset.caps
    exact if_pos (Or.inl hval)
  have hscan : Scanned.output row C 52 = Header.stream row := by
    change Prepare.output row 52 = _
    exact (install_slot Prepare.scanSlots (by decide) _ _ 0).trans (by rfl)
  rw [hnat, entry_old]
  simp only [WarmReuse.padded, hcap, ZeroPadding.pad_zero, Warm.input, Warm.supplied,
    Fin.addCases_left]
  exact hscan

/-- **The refutation, in one statement.**  A round of `WarmActual.machine`
(`Proof/CaseAnalysis/RowsEstimatorActual.lean`) leaves the externally owned native tape carrying
the printed cut stream of the row it just RAN — `WarmActual.native_run`
(`Proof/CaseAnalysis/CloseoutRowsEstimatorWarmRetained.lean`) retains it verbatim — while `entry_native` says
round `k+1` needs the NEXT row's stream there.  So the tapes the reusable bank protects cannot supply
the next row, and the residue of `reload_step` must be filled by the row writer. -/
theorem native_residue (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) (fuel : ℕ) (r : ExecutionReceipt _ _)
    (hr : runFrom (WarmActual.machine a) fuel
      (WarmActual.entry a row C Q q denominator select out) = some r) :
    r.final.tapes (Reuse.native (CompetitorCrossScheduler.producer a)) = Header.stream row := by
  rw [WarmActual.native_run a fuel _ r hr]
  exact entry_native (CompetitorCrossScheduler.producer a) (Warm.machine a) row C Q q denominator
    select (Driver.value a row.d row.p row.cuts.length C) out

end NearCubicWires.RepairSource.CloseoutFinal.C10InterRowReloader

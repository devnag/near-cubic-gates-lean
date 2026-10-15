import Proof.CaseAnalysis.RowsEstimatorPrepare
import Proof.CaseAnalysis.RowsEstimatorMetadataBatch
import Proof.MachineModel.Layout

/-! Paid scanner restart from a retained padded header and the row's three
produced scalar fields. The D backing and source fields are physical inputs;
this segment allocates neither. Its literal output is the existing Prepare
consumer's padded bank, with all source fields and reset tapes retained. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerReload
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.CloseoutRowsEstimator ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (row : EquationRow.Input) : Fin 3 → List Bool :=
  ![List.replicate row.d true, List.replicate row.p true, [row.odd]]
def extra (row : EquationRow.Input) (D : ℕ) : Fin 5 → List Bool :=
  ![fields row 0, fields row 1, fields row 2,
    List.replicate D true, List.replicate (D+1) false]
def caps (C D : ℕ) (i : Fin 64) := if i = 52 then C else D
def input (row : EquationRow.Input) (C D : ℕ) : Fin 69 → List Bool :=
  Fin.addCases (m:=64) (n:=5) (motive:=fun _ => List Bool) (fun i : Fin 64 => if i = 52 then ZeroPadding.pad C (Header.stream row)
    else List.replicate D false) (extra row D)
def middle (row : EquationRow.Input) (C D : ℕ) : Fin 69 → List Bool :=
  Fin.addCases (m:=64) (n:=5) (motive:=fun _ => List Bool) (fun i : Fin 64 => ZeroPadding.pad (caps C D i) (Prepare.input row i))
    (extra row D)
noncomputable def output (row : EquationRow.Input) (C D : ℕ) : Fin 69 → List Bool :=
  Fin.addCases (m:=64) (n:=5) (motive:=fun _ => List Bool) (fun i : Fin 64 => ZeroPadding.pad (caps C D i) (Prepare.output row i))
    (extra row D)
def copySlots : Fin 8 → Fin 69 := ![64,65,66,0,17,54,67,68]
noncomputable def first := RecoveryFocus.machine copySlots (MetadataBatch.machine 3)
noncomputable def last := TapeEmbedding.machine 5 Prepare.machine
noncomputable def machine := Composition.machine first last
def budget (row : EquationRow.Input) (D : ℕ) := (2*D+4)+1+Prepare.budget row

theorem copied (row : EquationRow.Input) (C D : ℕ) :
    install copySlots (input row C D) (MetadataBatch.output (fields row) D) =
      middle row C D := by
  funext i
  refine Fin.addCases (m:=64) (n:=5) (fun j => ?_) (fun j => ?_) i
  · by_cases h0 : j=0
    · subst j
      exact (install_slot copySlots (by decide) _ _ 3).trans (by rfl)
    by_cases h17 : j=17
    · subst j
      exact (install_slot copySlots (by decide) _ _ 4).trans (by rfl)
    by_cases h54 : j=54
    · subst j
      exact (install_slot copySlots (by decide) _ _ 5).trans (by rfl)
    have avoid : ∀ k, copySlots k ≠ j.castAdd 5 := by
      intro k he
      have hv := congrArg Fin.val he
      fin_cases k <;> dsimp [copySlots] at hv
      all_goals first
        | exact h0 (Fin.ext hv.symm)
        | exact h17 (Fin.ext hv.symm)
        | exact h54 (Fin.ext hv.symm)
        | omega
    rw [install_other _ _ _ _ avoid]
    simp only [input, middle, Fin.addCases_left, Prepare.input, h0, h17, h54, if_false, caps]
    split_ifs <;> simp [ZeroPadding.pad]
  · fin_cases j
    all_goals first
      | exact (install_slot copySlots (by decide) _ _ 0).trans (by rfl)
      | exact (install_slot copySlots (by decide) _ _ 1).trans (by rfl)
      | exact (install_slot copySlots (by decide) _ _ 2).trans (by rfl)
      | exact (install_slot copySlots (by decide) _ _ 6).trans (by rfl)
      | exact (install_slot copySlots (by decide) _ _ 7).trans (by rfl)

theorem run (row : EquationRow.Input) (C D : ℕ)
    (hd : row.d ≤ D) (hp : row.p ≤ D) (hD : 1 ≤ D) :
    Step machine (budget row D) (fun _ => 0) (input row C D)
      (fun _ => 0) (output row C D) := by
  have bound : ∀ i, (fields row i).length ≤ D := by
    intro i; fin_cases i <;> simpa [fields] using (by assumption)
  have copy := ((Step.of_ready (MetadataBatch.ready (fields row) D bound)).dock
    copySlots (by decide) (fun _ => 0) (input row C D) (by intro i; rfl)
    (by intro i; fin_cases i <;> rfl)).congr
      (dockH_existing copySlots (fun _ => 0) _ (by intro i; rfl)) (copied row C D)
  obtain ⟨r, hr, ht, hh, hs⟩ := Prepare.ready row
  have scan : Step Prepare.machine (Prepare.budget row) (fun _ => 0) (Prepare.input row)
      (fun _ => 0) (Prepare.output row) := ⟨r,hr,funext hh,ht,hs⟩
  have scan' := (scan.pad (caps C D)).embed (fun _ : Fin 5 => 0) (extra row D)
  have heads : Fin.addCases (m:=64) (n:=5) (motive:=fun _ => ℕ)
      (fun _ : Fin 64 => 0) (fun _ : Fin 5 => 0) =
      (fun _ : Fin 69 => 0) := by
    funext i
    refine Fin.addCases (m:=64) (n:=5) (fun _ => ?_) (fun _ => ?_) i <;> simp
  exact copy.seq ((scan'.congr_in heads rfl).congr heads rfl)

end NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerReload

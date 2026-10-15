import Proof.MachineModel.TopDownWorkspaceSelectedProgram
import Proof.MachineModel.TopDownAdmissionBudget

/-! The chosen physical admission has a degree fixed before k. The selected
capacity, cutoff, source and denominators are actual definitions, so this
statement has no free capacity or polynomial preprocessing premise. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedBudget
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceSelectedAdmission (originalTapes preFuel capacity coldCutoff)
noncomputable section

theorem degree_before_hierarchy (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) :
    ∃ degree,∀ (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))),
      ∃ coefficient,∀ n,preFuel sources p k clock n ≤ coefficient*(n+1)^degree := by
  obtain ⟨degree,hdegree⟩ := AdmissionBudget.degree_before_hierarchy
    (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) (coldCutoff sources)
    p.clauseDegree p.degree p.copies (capacity sources p).E (capacity sources p).K 1 1
    (CompetitorRationalGap.zeta (constantsOf sources)) p.hD
  refine ⟨degree,fun k clock => ?_⟩
  exact hdegree (SelectedSource.hierarchy sources k clock) (padding sources k clock)

/-- The same degree bounds the exact selected guarded worker's preprocessing;
its still-independent continuation cost remains visible and additive. -/
theorem guarded_degree_before_hierarchy (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) :
    ∃ degree,∀ (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (base extra : Nat)
      {bs : Nat} (continuation : Machine (originalTapes sources p k+1+1+extra) bs)
      (result : Fin (originalTapes sources p k+1+1+extra)) (bodyFuel : Nat → Nat),
      ∃ coefficient,∀ n,
        (GuardedAssembly.workerData sources p
          (WorkspaceSelectedProgram.programData sources p k clock base extra continuation result bodyFuel)).fuel n
        ≤ coefficient*(n+1)^degree+bodyFuel n := by
  obtain ⟨degree,hdegree⟩ := degree_before_hierarchy sources p
  refine ⟨degree,fun k clock base extra bs continuation result bodyFuel => ?_⟩
  obtain ⟨C,hC⟩ := hdegree k clock
  let D := WorkspaceSelectedProgram.programData sources p k clock base extra continuation result bodyFuel
  let W := GuardedAssembly.workerData sources p D
  refine ⟨C+4*W.onset+5,fun n => ?_⟩
  exact AdmissionBudget.guarded_fuel degree C W.onset n (preFuel sources p k clock) bodyFuel (hC n)

end
end NearCubicWires.P1TopDown.WorkspaceSelectedBudget

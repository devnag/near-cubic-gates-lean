import Proof.MachineModel.TopDownWorkspaceBoundedAdmission
import Proof.CaseAnalysis.WitnessBoundedFamilyPreHierarchy

/-! The actual parser plus cache rewind has a polynomial degree fixed before
the hierarchy. The hierarchy and final gate change only the coefficient.
This is the preprocessing part of Runtime; continuation cost remains explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.AdmissionBudget
open RepairOrdinary CloseoutWitness SourceInterfaces RepairSource RepairRepresentation
noncomputable section

theorem degree_before_hierarchy
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (cutoff D G copies E K symDen thrDen : Nat)
    (delta : Rat) (hD : 1≤D) :
    ∃ degree,∀ {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : Nat),
      ∃ coefficient,∀ n,
        2*WorkspaceBoundedAdmission.uniformFuel source a H Cpad cutoff D G copies E K
          symDen thrDen delta n+2 ≤ coefficient*(n+1)^degree := by
  obtain ⟨degree,hdegree⟩ := BudgetTools.degree_before_scale
    (ColdNative.bound_polynomial source a D G copies cutoff delta hD)
    (BoundedFamily.outer_polynomial source a G D copies E K symDen thrDen delta)
  refine ⟨degree,fun H Cpad => ?_⟩
  obtain ⟨C,hC⟩ := hdegree (HierarchyBudget.coefficient source H Cpad)
  refine ⟨4*C+2,fun n => ?_⟩
  have h := hC n
  have hp : 1≤(n+1)^degree := Nat.one_le_pow _ _ (by omega)
  dsimp only [WorkspaceBoundedAdmission.uniformFuel,HierarchyBudget.scale]
  nlinarith

/-- Apply the bound at the exact guarded worker fuel expression, without
claiming a bound for the still-unbuilt admitted continuation. -/
theorem guarded_fuel (degree coefficient onset n : Nat) (preFuel bodyFuel : Nat→Nat)
    (hpre : preFuel n≤coefficient*(n+1)^degree) :
    4*onset+5+preFuel n+bodyFuel n ≤
      (coefficient+4*onset+5)*(n+1)^degree+bodyFuel n := by
  have hp : 1≤(n+1)^degree := Nat.one_le_pow _ _ (by omega)
  nlinarith

end
end NearCubicWires.P1TopDown.AdmissionBudget

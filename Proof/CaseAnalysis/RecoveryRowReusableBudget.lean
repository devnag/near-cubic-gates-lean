import Proof.CaseAnalysis.RecoveryRowReusable

/-! Coarse cost of the complete reusable original row in its paid backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReusable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (u ref B : ℕ) (fields : Fin 78→List Bool)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B) :
    budget u ref B fields≤2*u+4*ref+49*B+67 := by
  have h:=RecoveryBoundedRowReload.budget_bound fields B hf
  unfold budget RecoveryBoundedRowAfter.budget
  omega

theorem budget_backing (u ref B : ℕ) (fields : Fin 78→List Bool)
    (hu : u≤B) (hr : ref≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B) :
    budget u ref B fields≤64*(B+2) := by
  have h:=budget_bound u ref B fields hf
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReusable

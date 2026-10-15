import Proof.MachineModel.P1ClosureCompactCost
import Proof.CaseAnalysis.RowsUniversalLoad

/-! The compact degree premise follows from the same actual digit load
already required by C.10, rather than a new bound on the selected row. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactModeCost
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutRawRows CloseoutRowsRawLogShape SupplierWalkBridge

theorem degree_le_width {q : Nat} (gs : List (SupportedNormalizedGate q))
    (L den z ell childBits : Nat) :
    z*coordinateDegree gs L den ≤ actualWidth gs L den z ell (childBits+1) := by
  rw [coordinateDegree_eq]
  unfold actualWidth rowWidth
  ring_nf
  omega

theorem degree_from_load {q : Nat} (gs : List (SupportedNormalizedGate q))
    (L den z ell childBits K s : Nat) (harity : s+K=q)
    (hload : 200*(K+actualWidth gs L den z ell (childBits+1)*(K+2)) ≤ s) :
    z*coordinateDegree gs L den ≤ q+1 := by
  have h := degree_le_width gs L den z ell childBits
  have hwidth : actualWidth gs L den z ell (childBits+1) ≤ s := by nlinarith
  omega

end NearCubicWires.P1Closure.CompactModeCost

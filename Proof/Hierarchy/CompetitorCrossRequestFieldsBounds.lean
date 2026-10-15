import Proof.Hierarchy.CompetitorCrossRequestFields
import Proof.MachineModel.OrdinaryMatrixCoefficientBounds

/-! The full original-request dimension producer remains quadratic in U.
Header scans, unary expansion, all copies, sums, products and resets are paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossRequestFields
open RepairSource.ProjectionNormalization MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem headers_bound (r : Request) : CompetitorCrossRequestHeaders.budget r ≤
    1000*(r.U+1)*(r.d+r.p+1)^2 := by
  have hpart : CompetitorCrossRequestHeaders.budget r ≤ MatrixCoefficientCold.budget r := by
    unfold CompetitorCrossRequestHeaders.budget CompetitorCrossRequestHeaders.suffix
      MatrixCoefficientCold.budget MatrixCoefficientCold.forwardBudget MatrixCoefficientHeaders.budget
    omega
  exact hpart.trans (MatrixCoefficientBounds.coefficient_budget r)

theorem budget_bound (r : Request) : budget r ≤ 5000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hh := headers_bound r
  unfold budget CompetitorCrossRequestDimensions.budget CompetitorCrossRequestHeaders.powerBudget
    MatrixScorePower.budget MatrixUnaryTemplate.budget
  rw [show 2^r.d=r.U from rfl]
  simp only [DimensionPower.cost,WilliamsUnaryProduct.budget]
  ring_nf at hh ⊢
  omega

end NearCubicWires.RepairOrdinary.CompetitorCrossRequestFields

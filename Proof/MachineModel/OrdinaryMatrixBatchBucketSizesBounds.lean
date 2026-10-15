import Proof.MachineModel.OrdinaryMatrixBatchBucketSizes

/-! Full original-request canonical dimension cost, including every
quotient, physical branch and retained-driver docking call. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketSizesBounds
open MatrixScoreBatch SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_value_le (r : Request) : MatrixBucketDimensions.bucketBudget r.U r.Gates≤r.U := by
  have hU : 1≤r.U := Nat.one_le_two_pow
  have hc := MatrixBucketDimensions.capacity_le r.U
  unfold MatrixBucketDimensions.bucketBudget stableCapacityBucketBudget
  split
  · exact hU
  · exact (Nat.div_le_self _ _).trans hc

theorem budget_le (r : Request) :
    MatrixBatchBucketSizes.budget r≤3*10^10*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hr := MatrixBatchRootCapacityBounds.budget_le r
  unfold MatrixBatchRootCapacityBounds.envelope at hr
  have hs := MatrixBucketSizes.budget_le r.U (MatrixBucketDimensions.bucketBudget r.U r.Gates)
  have hq := budget_value_le r
  have hc := MatrixBucketDimensions.capacity_le r.U
  have hw : 1≤(r.d+r.p+1)^2 := by
    have hp : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hmul := Nat.mul_le_mul_left ((r.U+1)^2) hw
  have he : r.U+1≤(r.U+1)^2*(r.d+r.p+1)^2 := by nlinarith
  unfold MatrixBatchBucketSizes.budget MatrixBatchBucketBudget.budget MatrixBucketBudget.budget
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchBucketSizesBounds

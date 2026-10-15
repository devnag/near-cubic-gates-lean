import Proof.MachineModel.OrdinaryMatrixBatchBucketUsage

/-! All canonical native/unary dimensions and their docking costs fit the
full quadratic raw-request preprocessing envelope. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchDimensionsBounds
open MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def envelope (r : Request) := 4*10^10*(r.U+1)^2*(r.d+r.p+1)^2
theorem dimension_le (r : Request) (j : Fin 3) : MatrixBatchNativeDimensions.dimensions r j≤2*r.U+1 := by
  fin_cases j
  · exact (MatrixBucketDimensions.capacity_le r.U).trans (by omega)
  · exact MatrixBucketDimensions.width_le r.U r.Gates
  · exact MatrixBucketDimensions.buckets_le r.U r.Gates
theorem native_budget_le (r : Request) :
    MatrixNativeDimensions.budget r.M (MatrixBatchNativeDimensions.dimensions r)≤
      10000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hn (j : Fin 3) := dimension_le r j
  have hp (j : Fin 3) := Nat.pow_le_pow_left (hn j) 2
  have hsingle (j : Fin 3) : MatrixNativeDimension.budget r.M (MatrixBatchNativeDimensions.dimensions r j)≤
      16*(2*r.U+1)^2+76*(2*r.U+1)+4*r.M+50 := by
    unfold MatrixNativeDimension.budget
    nlinarith [hn j,hp j]
  have hM : r.M≤3*(r.d+r.p+1) := by rw [common_width]; omega
  have hw : 1≤(r.d+r.p+1)^2 := by
    have h : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hu : 1≤(r.U+1)^2 := by
    have h : 0<(r.U+1)^2 := by positivity
    omega
  have h1 := Nat.mul_le_mul_left ((r.U+1)^2) hw
  have h2 := Nat.mul_le_mul_right ((r.d+r.p+1)^2) hu
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  unfold MatrixNativeDimensions.budget
  nlinarith [hsingle 0,hsingle 1,hsingle 2]

theorem usage_budget_le (r : Request) : MatrixBucketUsage.budget r.Gates r.Buckets r.Capacity≤20*r.U+37 := by
  have hused := capacity r
  have hc : r.Capacity≤r.U := MatrixBucketDimensions.capacity_le r.U
  have hG : r.Gates≤r.Capacity := (Nat.le_mul_self r.Gates).trans r.gateSquare
  unfold MatrixBucketUsage.budget Request.Used at *
  nlinarith

theorem budget_le (r : Request) : MatrixBatchBucketUsage.budget r≤envelope r := by
  have hbase := MatrixBatchBucketSizesBounds.budget_le r
  have hnative := native_budget_le r
  have husage := usage_budget_le r
  have hM : r.M≤3*(r.d+r.p+1) := by rw [common_width]; omega
  have hw : 1≤(r.d+r.p+1)^2 := by
    have h : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hu : 1≤(r.U+1)^2 := by
    have h : 0<(r.U+1)^2 := by positivity
    omega
  have h1 := Nat.mul_le_mul_left ((r.U+1)^2) hw
  have h2 := Nat.mul_le_mul_right ((r.d+r.p+1)^2) hu
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  unfold MatrixBatchBucketUsage.budget MatrixBatchNativeDimensions.budget MatrixBatchNativeWidth.budget envelope
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchDimensionsBounds

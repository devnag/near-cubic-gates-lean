import Proof.MachineModel.OrdinaryMatrixRankPacketLoad

/-! The complete raw rank/dimension/rewind prefix preserves the stated
quadratic preprocessing envelope, with all returned cursors charged. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRankReverseBounds
open MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reverse_budget (r : Request) : MatrixRankReverseEntry.budget (H r) r.U r.Gates ≤
    200*(r.U+1)^2*(r.d+r.p+1) := by
  have hH : H r ≤ 8*(r.d+r.p+1) := by
    have h := MatrixScoreRawRanksBounds.header_width r
    unfold H
    omega
  have hG : r.Gates ≤ r.U := (Nat.le_mul_self r.Gates).trans
    (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hq : 1 ≤ r.d+r.p+1 := by omega
  have hfield := Nat.mul_le_mul_left (2*r.U) (show 5*H r+6 ≤ 46*(r.d+r.p+1) by omega)
  have hterm : 2*r.U*(5*H r+6)+12 ≤ 104*(r.U+1)*(r.d+r.p+1) := by nlinarith
  have hgate := Nat.mul_le_mul hG hterm
  unfold MatrixRankReverseEntry.budget MatrixRankStreamReverse.budget MatrixRankStreamReverse.loopBudget
    MatrixRankPacketReverse.budget MatrixRankRowReverse.budget MatrixRankFieldReverse.budget
  nlinarith

theorem budget_le (r : Request) : MatrixBatchRankReverse.budget r ≤
    5*10^10*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hbase := MatrixBatchDimensionsBounds.budget_le r
  have hreverse := reverse_budget r
  have hH : H r ≤ 8*(r.d+r.p+1) := by
    have h := MatrixScoreRawRanksBounds.header_width r
    unfold H
    omega
  have hM : r.M ≤ 3*(r.d+r.p+1) := by rw [common_width]; omega
  have hu : 1 ≤ (r.U+1)^2 := by
    have hp : 0<(r.U+1)^2 := by positivity
    omega
  have hq : r.d+r.p+1 ≤ (r.d+r.p+1)^2 := by nlinarith
  have h1 := Nat.mul_le_mul_left ((r.U+1)^2) hq
  have h2 := Nat.mul_le_mul_right (r.d+r.p+1) hu
  unfold MatrixBatchRankReverse.budget MatrixBatchBucketEndpoints.budget MatrixBucketEndpoints.budget
  unfold MatrixBatchDimensionsBounds.envelope at hbase
  unfold H at hH
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchRankReverseBounds

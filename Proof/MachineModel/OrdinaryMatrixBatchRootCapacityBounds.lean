import Proof.MachineModel.OrdinaryMatrixBatchRootCapacity

namespace NearCubicWires.RepairOrdinary.MatrixBatchRootCapacityBounds
open MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def envelope (r : Request) := 20000000000*(r.U+1)^2*(r.d+r.p+1)^2
theorem budget_le (r : Request) : MatrixBatchRootCapacity.budget r≤envelope r := by
  have hs : r.Gates*r.Gates≤r.U := r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U)
  have hg : r.Gates≤r.U := by nlinarith
  have hr := MatrixBatchAllRanksBounds.budget_le r
  have hrecord : MatrixBatchAllRanks.budget r≤10000000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
    apply hr.trans
    unfold MatrixBatchAllRanksBounds.envelope
    calc 10000000000*(r.Gates+1)*(r.U+1)*(r.d+r.p+1)^2
        ≤10000000000*(r.U+1)*(r.U+1)*(r.d+r.p+1)^2 := by gcongr
      _ = _ := by ring
  have hD := Nat.mul_le_mul_left (r.U+1) (MatrixBatchAllRanksBounds.storage_bound r)
  have hsq : 1≤(r.d+r.p+1)^2 := by
    have hp : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hu := Nat.mul_le_mul_left (r.U+1) hsq
  unfold MatrixBatchRootCapacity.budget MatrixBucketRootCold.budget MatrixBucketRootLoop.budget
    MatrixBucketRootLoop.roundBudget envelope
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchRootCapacityBounds

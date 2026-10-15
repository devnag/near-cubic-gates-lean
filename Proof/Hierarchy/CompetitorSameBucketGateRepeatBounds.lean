import Proof.Hierarchy.CompetitorSameBucketGateNative

/-! The full streamed gate repetition retains the tight gate-square cost,
then charges both loads and every sentinel transition. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateLoop
open LocalBitMultitape MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request dimension_positive)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem all_gate_polynomial (r : Request) :
    budget r (CompetitorSameBucketBucketBody.scalarCapacity r) r.Gates≤6000000000*r.U^2*(r.d+r.p+1)^2 := by
  have ha:=CompetitorSameBucketGate.all_gate_polynomial r
  have hg : r.Gates≤r.U := (Nat.le_mul_self r.Gates).trans (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hu:=dimension_positive r
  have hu2 : r.U≤r.U^2 := by nlinarith
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have hq1 : 1≤(r.d+r.p+1)^2 := by nlinarith
  have hGU : r.Gates≤r.U^2 := hg.trans hu2
  have hUQ0 : r.U^2≤r.U^2*(r.d+r.p+1)^2 := by simpa using Nat.mul_le_mul_left (r.U^2) hq1
  have hGQ := hGU.trans hUQ0
  have hUQ : 1≤r.U^2*(r.d+r.p+1)^2 := by nlinarith
  have hD := Nat.mul_le_mul hg (MatrixBatchAllRanksBounds.storage_bound r)
  have hC : CompetitorSameBucketBucketBody.scalarCapacity r≤262162*(r.d+r.p+1)^2 :=
    (by omega : CompetitorSameBucketBucketBody.scalarCapacity r≤
      CompetitorSameBucketBucketBody.scalarCapacity r+H r+r.M+r.p+1).trans
      (CompetitorSameBucketGate.scalar_quantum_bound r)
  have hGC:=Nat.mul_le_mul hGU hC
  have hp : r.p≤(r.d+r.p+1)^2 := (by omega : r.p≤r.d+r.p+1).trans hq
  have hGP:=Nat.mul_le_mul hGU hp
  unfold budget CompetitorSameBucketGateBody.fuel
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateLoop

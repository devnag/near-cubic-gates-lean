import Proof.Hierarchy.CompetitorSameBucketGate

/-! Sum the actual native-gate costs with gateSquare before substituting
capacities. This preserves the U² aggregate even for the large-B branch. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGate
open LocalBitMultitape MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request dimension_positive)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem gate_budget_bound (r : Request) (cap : ℕ) :
    budget r cap≤r.Buckets*(2*MatrixScoreReusableRanks.D r+
      600*(r.bucketSize+1)^2*(cap+H r+r.M+r.p+1))+7 := by
  have hb := CompetitorSameBucketBucketBody.budget_bound r (MatrixScoreReusableRanks.D r) cap (r.bucketSize+1) (by omega)
  have hB : r.bucketSize+1≤(r.bucketSize+1)^2 := by nlinarith
  have hB1 : 1≤(r.bucketSize+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_right (5*H r+6) hB
  have hs : CompetitorSameBucketBucketBody.budget r (MatrixScoreReusableRanks.D r) cap (r.bucketSize+1)+
      MatrixRankRowReverse.budget (H r) (r.bucketSize+1)+6≤
      2*MatrixScoreReusableRanks.D r+600*(r.bucketSize+1)^2*(cap+H r+r.M+r.p+1) := by
    unfold MatrixRankRowReverse.budget MatrixRankFieldReverse.budget
    nlinarith
  have hmul := Nat.mul_le_mul_left r.Buckets hs
  unfold budget CompetitorSameBucketGateScan.budget CompetitorSameBucketBucketLoop.budget CompetitorSameBucketPacketReturn.budget
  nlinarith

theorem all_gate_budget (r : Request) (cap : ℕ) :
    r.Gates*budget r cap≤2*(r.Gates*r.Buckets)*MatrixScoreReusableRanks.D r+
      15000*r.U^2*(cap+H r+r.M+r.p+1)+7*r.Gates := by
  have h := Nat.mul_le_mul_left r.Gates (gate_budget_bound r cap)
  have hs := Nat.mul_le_mul_right (600*(cap+H r+r.M+r.p+1)) (CompetitorSameBucket.request_all_pairs r)
  nlinarith

theorem scalar_quantum_bound (r : Request) :
    CompetitorSameBucketBucketBody.scalarCapacity r+H r+r.M+r.p+1≤262162*(r.d+r.p+1)^2 := by
  have hh : H r+1≤8*(r.d+r.p+1) := by simpa only [H,Nat.add_assoc] using MatrixScoreRawRanksBounds.header_width r
  have hs := Nat.pow_le_pow_left hh 2
  have hm : r.M≤H r := by unfold H; omega
  have hp : r.p≤r.d+r.p+1 := by omega
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have hq1 : 1≤(r.d+r.p+1)^2 := by nlinarith
  unfold CompetitorSameBucketBucketBody.scalarCapacity CompetitorReusableDecision.capacity
  nlinarith

theorem all_gate_polynomial (r : Request) :
    r.Gates*budget r (CompetitorSameBucketBucketBody.scalarCapacity r)≤5000000000*r.U^2*(r.d+r.p+1)^2 := by
  have ha := all_gate_budget r (CompetitorSameBucketBucketBody.scalarCapacity r)
  have hc : r.Gates*r.Buckets≤r.U := (MatrixScoreBatch.capacity r).trans (WilliamsPaddedRequest.inner_le r.U)
  have hd := MatrixBatchAllRanksBounds.storage_bound r
  have hmul := Nat.mul_le_mul hc hd
  have hscalar := Nat.mul_le_mul_left (15000*r.U^2) (scalar_quantum_bound r)
  have hg : r.Gates≤r.U := (Nat.le_mul_self r.Gates).trans (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hu := dimension_positive r
  have hq : 1≤(r.d+r.p+1)^2 := by nlinarith
  have huq := Nat.mul_le_mul_left (r.U^2) hq
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGate

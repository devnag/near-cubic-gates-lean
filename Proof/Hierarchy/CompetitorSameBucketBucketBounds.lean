import Proof.Hierarchy.CompetitorSameBucketBucketBody

/-! The actual whole-bucket machine uses the tight B² currency; its D erase
is paid once per bucket. Existing native capacities discharge the two-sided
copy workspace bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketBody
open LocalBitMultitape MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request dimension_positive)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (r : Request) (d cap b : ℕ) (hb : 1≤b) :
    budget r d cap b≤2*d+500*b^2*(cap+H r+r.M+r.p+1) := by
  have hs := CompetitorSameBucketSquare.budget_bound r cap b hb
  have he : CompetitorSameBucketBucketPrepare.budget d (H r) b=2*d+b*(21*H r+10)+19 := by
    unfold CompetitorSameBucketBucketPrepare.budget CompetitorSameBucketBlockLoad.budget
      CompetitorSameBucketRecordCopy.budget MatrixRankRowReverse.budget MatrixRankFieldReverse.budget
    ring
  unfold budget
  rw [he]
  have hB : b≤b^2 := by nlinarith
  have hB1 : 1≤b^2 := by nlinarith
  have hm := Nat.mul_le_mul_right (21*H r+10) hB
  nlinarith

theorem native_packet_copy_fit (r : Request) :
    2*(CompetitorSameBucketPackets.count r*CompetitorSameBucketPackets.width r)+4≤MatrixScoreReusableRanks.D r := by
  have hc := (CompetitorSameBucketPackets.count_bounds r).2
  have hH : H r≤8*(r.d+r.p+1) := by have h := MatrixScoreRawRanksBounds.header_width r; unfold H; omega
  have hw : CompetitorSameBucketPackets.width r≤33*(r.d+r.p+1) := by unfold CompetitorSameBucketPackets.width; omega
  have hm := Nat.mul_le_mul hc hw
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have hprod := Nat.mul_le_mul_left (330*r.U) hq
  have hd := MatrixScoreReusableRanks.capacity_gap r
  unfold MatrixScoreRawRanksBounds.capacity at hd
  have hq1 : 1≤(r.d+r.p+1)^2 := by nlinarith
  nlinarith

theorem native_bucket_copy_fit (r : Request) :
    2*((r.bucketSize+1)*CompetitorSameBucketPackets.width r)+4≤MatrixScoreReusableRanks.D r := by
  have hc : r.bucketSize+1≤CompetitorSameBucketPackets.count r := by
    have hb : 1≤r.Buckets := Nat.succ_le_succ (Nat.zero_le _)
    unfold CompetitorSameBucketPackets.count
    nlinarith
  have hm := Nat.mul_le_mul_right (CompetitorSameBucketPackets.width r) hc
  have hp := native_packet_copy_fit r
  omega

def scalarCapacity (r : Request) := CompetitorReusableDecision.capacity (H r)
theorem scalar_capacity_fits (r : Request) :
    30*(H r+1) ≤ scalarCapacity r ∧ 2*(r.p+1)+1 ≤ scalarCapacity r := by
  have hp : r.p≤H r := by unfold H MatrixScoreBatch.Request.S; omega
  unfold scalarCapacity CompetitorReusableDecision.capacity
  constructor <;> nlinarith

theorem all_bucket_body_bound (r : Request) (d cap : ℕ) :
    r.Gates*r.Buckets*budget r d cap (r.bucketSize+1)≤
      2*(r.Gates*r.Buckets)*d+12500*r.U^2*(cap+H r+r.M+r.p+1) := by
  have hb := budget_bound r d cap (r.bucketSize+1) (by omega)
  have hm := Nat.mul_le_mul_left (r.Gates*r.Buckets) hb
  have hp := CompetitorSameBucket.request_all_pairs r
  have hmul := Nat.mul_le_mul_right (500*(cap+H r+r.M+r.p+1)) hp
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketBody

import Proof.Hierarchy.CompetitorSameBucketColdGate

/-! Whole cold-gate ledger, including original rank/coefficient preparation,
physical dimensions, both allocations, all five copies, and all G gates. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdGate
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (r : Request) : budget r≤70000000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let z:=(r.U+1)^2*(r.d+r.p+1)^2
  have hu:=MatrixScoreBatch.dimension_positive r
  have q2 : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have u2 : r.U≤(r.U+1)^2 := by nlinarith
  have qz : (r.d+r.p+1)^2≤z := by
    have h : 1≤(r.U+1)^2 := by nlinarith
    exact Nat.le_mul_of_pos_left _ (by omega)
  have uz : r.U≤z := by
    have h : 1≤(r.d+r.p+1)^2 := by nlinarith
    have hm:=Nat.mul_le_mul_left ((r.U+1)^2) h
    dsimp only [z]
    nlinarith
  have zpos : 1≤z := by
    have h : 0<z := by dsimp only [z]; positivity
    omega
  have cBound : CompetitorSameBucketBucketBody.scalarCapacity r≤262162*z := by
    have h:=CompetitorSameBucketGate.scalar_quantum_bound r
    nlinarith
  have dBound : MatrixScoreReusableRanks.D r≤200000000*z := by
    have h:=MatrixBatchAllRanksBounds.storage_bound r
    have hm:=Nat.mul_le_mul_right ((r.d+r.p+1)^2) u2
    dsimp only [z]
    nlinarith
  have hBound : H r≤8*z := by
    have h:=MatrixScoreRawRanksBounds.header_width r
    change H r+1≤8*(r.d+r.p+1) at h
    omega
  have mBound : r.M≤8*z := by unfold H at hBound; omega
  have pBound : r.p≤z := by omega
  have bBound : r.bucketSize+1≤3*z := by
    have h : r.bucketSize+1≤2*r.U+1:=CompetitorSameBucket.block_width_le r.U r.Capacity r.Gates
    omega
  have block : (4*H r+1)*(r.bucketSize+1)≤MatrixScoreReusableRanks.D r := by
    have hb : 1≤r.Buckets := Nat.succ_le_succ (Nat.zero_le _)
    have hsmall : r.bucketSize+1≤r.Buckets*(r.bucketSize+1) := by nlinarith
    have hm:=Nat.mul_le_mul_left (4*H r+1) hsmall
    have h:=CompetitorSameBucketPackets.packet_fits r
    change r.Buckets*(r.bucketSize+1)*(4*H r+1)≤MatrixScoreReusableRanks.D r at h
    nlinarith
  have cold:=CompetitorSameBucketCold.budget_le r
  have gates:=CompetitorSameBucketGateLoop.all_gate_polynomial r
  have gu : r.U^2≤(r.U+1)^2 := by nlinarith
  have gm:=Nat.mul_le_mul_right ((r.d+r.p+1)^2) gu
  have dims:=CompetitorDimensions.budget_bound (H r)
  change CompetitorDimensions.budget (H r)≤10*CompetitorSameBucketBucketBody.scalarCapacity r at dims
  unfold budget CompetitorSameBucketColdInitialized.budget CompetitorSameBucketColdWorkspace.budget
    CompetitorSameBucketColdCoefficient.budget CompetitorSameBucketColdBlocks.budget CompetitorSameBucketColdCapacity.budget
    CompetitorSameBucketColdAllocate.budget CompetitorSameBucketColdCopies.budget
    CompetitorSameBucketCoefficientTemplate.budget CompetitorDimensions.bootstrapBudget
  rw [CompetitorSameBucketBlockDrivers.budget_eq]
  dsimp only [z] at *
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdGate

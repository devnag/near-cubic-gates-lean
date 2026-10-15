import Proof.Hierarchy.CompetitorSameBucketKeyRecords

/-! Full cold gate-plus-zero-grid envelope. Both the original gate work
and every newly executed allocation/copy/zero-cell step are included. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdZeroGrid
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (r : Request) : budget r≤71000000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let z:=(r.U+1)^2*(r.d+r.p+1)^2
  have qpos : 1≤(r.d+r.p+1)^2 := by
    have h : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have upos : 1≤(r.U+1)^2 := by
    have h : 0<(r.U+1)^2 := by positivity
    omega
  have qz : (r.d+r.p+1)^2≤z := by
    have h:=Nat.mul_le_mul_right ((r.d+r.p+1)^2) upos
    simpa only [Nat.one_mul] using h
  have uz : r.U≤z := by
    have h:=Nat.mul_le_mul_left ((r.U+1)^2) qpos
    dsimp only [z]
    nlinarith
  have zpos : 1≤z := by omega
  have scalar:=CompetitorSameBucketGate.scalar_quantum_bound r
  have scalarZ : CompetitorSameBucketBucketBody.scalarCapacity r+r.p+r.M+1≤262162*z := by omega
  have scalarQ : CompetitorSameBucketBucketBody.scalarCapacity r+r.p+r.M+1≤262162*(r.d+r.p+1)^2 := by omega
  have square : r.U^2+1≤(r.U+1)^2 := by nlinarith
  have product:=Nat.mul_le_mul square scalarQ
  have gridBound:=CompetitorSameBucketZeroGrid.budget_bound r.p r.M r.U (CompetitorSameBucketBucketBody.scalarCapacity r)
  have gridZ : CompetitorSameBucketZeroGrid.budget r.p r.M r.U (CompetitorSameBucketBucketBody.scalarCapacity r) r.U≤26216200*z := by
    dsimp only [z]
    nlinarith
  have gates:=CompetitorSameBucketColdGate.budget_bound r
  unfold budget CompetitorSameBucketZeroGridCold.budget CompetitorSameBucketZeroPrepareCopies.budget
    CompetitorSameBucketZeroPrepareSpace.budget CompetitorSameBucketZeroPrepareCopies.copyBudget
  dsimp only [z] at *
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdZeroGrid

import Proof.Hierarchy.CompetitorSameBucketGateBody

/-! One uniform fuel for the actual streamed gate body, with both input
loads charged. The enclosing physical Gates loop uses this bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateBody
open LocalBitMultitape RecoveryExecution MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fuel (r : Request) (cap : ℕ) :=
  CompetitorSameBucketGate.budget r cap+4*MatrixScoreReusableRanks.D r+2*cap+4*r.p+22

theorem budget_le (r : Request) (cap : ℕ) (gate : Fin r.Gates) : budget r cap gate≤fuel r cap := by
  have h:=MatrixBatchRankedGate.packet_fits r gate
  have hl : (CompetitorSameBucketGatePrepare.bits r gate).length=r.p+1 := by
    simp [CompetitorSameBucketGatePrepare.bits]
  unfold budget CompetitorSameBucketGatePrepare.budget CompetitorSameBucketGateLoad.packetBudget
    CompetitorSameBucketGateLoad.coefficientBudget MatrixRankPacketLoad.budget
    CompetitorSameBucketCoefficientLoad.budget fuel
  rw [hl]
  omega

theorem source_fits (r : Request) (gate : Fin r.Gates) :
    (CompetitorSameBucketGateScan.source r gate).length≤MatrixScoreReusableRanks.D r := by
  unfold CompetitorSameBucketGateScan.source
  rw [ZeroPadding.pad_length]
  apply max_le (Nat.le_refl _)
  rw [←MatrixBatchRankedGate.stream_eq]
  apply le_trans _ (MatrixBatchRankedGate.packet_fits r gate)
  simp only [MatrixBatchRankAppend.stream,MatrixBatchRankAppend.packetBudget,
    List.length_append,List.length_singleton]
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateBody

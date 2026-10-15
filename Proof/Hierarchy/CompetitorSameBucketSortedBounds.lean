import Proof.Hierarchy.CompetitorSameBucketSorted

/-! The full cold sorted-key parent retains quadratic work in U. The
26U² real record bound includes both padded candidates and the zero grid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdSorted
open MatrixScoreBatch (Request)
open CompetitorSameBucketKeyRecords (records)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem local_budget_bound (r : Request) : localBudget r≤600000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let request : SortCarrier.Request:=⟨records r,CompetitorSameBucketKeyRecords.sort_uniform r⟩
  have sortBound:=SortCost.carrier_budget_le request
  change 4*(StablePartition.stream (records r)).length+3+SortCarrier.budget (records r)≤
    128*((records r).length+1)*(SortPreparation.width (records r)+1)^2 at sortBound
  have count : (records r).length+1≤27*(r.U+1)^2 := by
    have h:=CompetitorSameBucketKeyRecords.records_length r
    have square : r.U^2+1≤(r.U+1)^2 := by nlinarith [Nat.zero_le r.U]
    omega
  have width : SortPreparation.width (records r)+1≤9*(r.d+r.p+1) := by
    rw [CompetitorSameBucketKeyRecords.sort_width,MatrixScoreBatch.common_width]
    omega
  have product:=Nat.mul_le_mul count (Nat.pow_le_pow_left width 2)
  have pos : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have h : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold localBudget
  nlinarith

theorem budget_bound (r : Request) : budget r≤160000000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have source:=CompetitorSameBucketColdKeyStream.budget_bound r
  have sorted:=local_budget_bound r
  have pos : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have h : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdSorted

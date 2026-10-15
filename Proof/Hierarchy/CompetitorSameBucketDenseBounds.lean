import Proof.Hierarchy.CompetitorSameBucketDense

/-! The entire canonical dense-bank producer uses only d,p short widths.
All physical scalar generation, allocation, sorting, grouping, calls and
rewinds remain charged in the actual quadratic-in-U bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_eq (r : Request) : width r=r.d+2*r.p+3 := by
  simp only [width,CompetitorPlaneWidth.width,MatrixScoreBatch.Request.U]
  have hb : natBitLength (2^r.d)=r.d+1 := by simp [natBitLength,Nat.log_pow]
  rw [hb]
  omega

theorem short_fields (r : Request) : width r+r.p+r.M+1 ≤ 7*(r.d+r.p+1) := by
  rw [width_eq,MatrixScoreBatch.common_width]
  omega

theorem group_budget_bound (r : Request) :
    groupBudget r ≤ 29400000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hg:=CompetitorSameBucketGroupCold.budget_bound (width r) r.U r.p r.M
    (CompetitorSameBucketEntries.entries r) (CompetitorSameBucketEntries.length_bound r)
  have hfields:=Nat.pow_le_pow_left (short_fields r) 2
  have hm:=Nat.mul_le_mul_left (600000*(r.U+1)^2) hfields
  change groupBudget r ≤ _ at hg
  nlinarith

theorem budget_bound (r : Request) :
    budget r ≤ 161000000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hs:=CompetitorSameBucketColdSorted.budget_bound r
  have hg:=group_budget_bound r
  have hp : 1 ≤ (r.U+1)^2*(r.d+r.p+1)^2 := by
    have h : 0 < (r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense

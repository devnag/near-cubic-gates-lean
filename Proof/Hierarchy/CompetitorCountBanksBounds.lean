import Proof.Hierarchy.CompetitorCountBanks
import Proof.Hierarchy.CompetitorSameBucketDenseBounds

/-! Complete both-bank runtime including the actual same-bucket sort/group
and all cross-table preparation. Source logarithmic dependence is unchanged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountBanks
open RepairRepresentation MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coefficient (a : WilliamsAlgorithm) := CompetitorCrossScheduler.coefficient a+161000000001
noncomputable def envelope (a : WilliamsAlgorithm) (r : Request) :=
  coefficient a*(r.U+1)^2*(r.d+r.p+1)^CompetitorCrossScheduler.exponent a

theorem budget_eq (a : WilliamsAlgorithm) (r : Request) :
    budget a r=CompetitorCrossScheduler.budget a r+CompetitorSameBucketColdDense.budget r+1 := by
  unfold budget prefixBudget CompetitorCrossScheduler.budget
  omega

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) : budget a r+1 ≤ envelope a r := by
  have hc := CompetitorCrossScheduler.budget_bound a r
  have hs := CompetitorSameBucketColdDense.budget_bound r
  have hp : (r.d+r.p+1)^2 ≤ (r.d+r.p+1)^CompetitorCrossScheduler.exponent a :=
    Nat.pow_le_pow_right (by omega) (by unfold CompetitorCrossScheduler.exponent;omega)
  have hm := Nat.mul_le_mul_left (161000000000*(r.U+1)^2) hp
  have hs' := hs.trans hm
  let mass := (r.U+1)^2*(r.d+r.p+1)^CompetitorCrossScheduler.exponent a
  have hpos : 1 ≤ mass := by
    have h : 0 < mass := by dsimp [mass];positivity
    omega
  unfold CompetitorCrossScheduler.envelope at hc
  rw [Nat.mul_assoc] at hc hs'
  change CompetitorCrossScheduler.budget a r+1 ≤ CompetitorCrossScheduler.coefficient a*mass at hc
  change CompetitorSameBucketColdDense.budget r ≤ 161000000000*mass at hs'
  rw [budget_eq]
  unfold envelope coefficient
  rw [Nat.mul_assoc]
  change CompetitorCrossScheduler.budget a r+CompetitorSameBucketColdDense.budget r+1+1 ≤
    (CompetitorCrossScheduler.coefficient a+161000000001)*mass
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorCountBanks

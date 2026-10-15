import Proof.Hierarchy.CompetitorCountTable

/-! Whole natural-count runtime: the fixed final-table work adds a quadratic
short-width term to the already paid Williams/same/cross envelope. No raw
U-sized quantity is inserted into a field-width exponent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open RepairRepresentation MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coefficient (a : WilliamsAlgorithm) := CompetitorCountBanks.coefficient a+9952003
noncomputable def envelope (a : WilliamsAlgorithm) (r : Request) :=
  coefficient a*(r.U+1)^2*(r.d+r.p+1)^CompetitorCrossScheduler.exponent a

theorem final_bound (r : Request) (q : ℕ) (hq : q≤CompetitorSameBucketColdDense.width r) :
    CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q≤
      9952000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hf := CompetitorFinalTable.budget_bound r.U (CompetitorSameBucketColdDense.width r) q hq
  have hw : CompetitorSameBucketColdDense.width r+1≤4*(r.d+r.p+1) := by
    rw [CompetitorSameBucketColdDense.width_eq]
    omega
  have hu : r.U*r.U+1≤(r.U+1)^2 := by nlinarith
  apply hf.trans
  calc
    _ ≤ 622000*(r.U+1)^2*(4*(r.d+r.p+1))^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 622000 hu) (Nat.pow_le_pow_left hw 2)
    _ = _ := by ring

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) (q : ℕ)
    (hq : q≤CompetitorSameBucketColdDense.width r) : budget a r q+1≤envelope a r := by
  have hb := CompetitorCountBanks.budget_bound a r
  have hf := final_bound r q hq
  have hp : (r.d+r.p+1)^2≤(r.d+r.p+1)^CompetitorCrossScheduler.exponent a :=
    Nat.pow_le_pow_right (by omega) (by unfold CompetitorCrossScheduler.exponent;omega)
  have hf' := hf.trans (Nat.mul_le_mul_left (9952000*(r.U+1)^2) hp)
  let mass := (r.U+1)^2*(r.d+r.p+1)^CompetitorCrossScheduler.exponent a
  have hm : 1 ≤ mass := by
    have h : 0 < mass := by dsimp [mass];positivity
    omega
  unfold CompetitorCountBanks.envelope at hb
  rw [Nat.mul_assoc] at hb hf'
  change CompetitorCountBanks.budget a r+1≤CompetitorCountBanks.coefficient a*mass at hb
  change CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q≤9952000*mass at hf'
  unfold budget prefixBudget envelope coefficient
  rw [Nat.mul_assoc]
  change CompetitorCountBanks.budget a r+2+1+
    CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q+1≤
    (CompetitorCountBanks.coefficient a+9952003)*mass
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorCountTable

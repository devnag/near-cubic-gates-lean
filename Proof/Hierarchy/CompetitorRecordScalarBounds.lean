import Proof.Hierarchy.CompetitorRecordScalar

/-! The complete record-scalar caller has cubic record-count dependence
and quadratic bit-width dependence, including all cold metadata production. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRecordScalar
open CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem common_width_eq (b l n : ℕ) :
    CompetitorProducedScalar.commonWidth b l n=(width b+(l+1))*(n+1) := by
  unfold CompetitorProducedScalar.commonWidth CompetitorThresholdCold.runtimeWidth CompetitorSumWidth.width
  ring

theorem driver_bound (b l n : ℕ) : CompetitorRecordScalarDrivers.budget b l n≤
    50000*(CompetitorProducedScalar.commonWidth b l n+1)^2 := by
  let t := CompetitorProducedScalar.commonWidth b l n
  have ht := common_width_eq b l n
  change t=(width b+(l+1))*(n+1) at ht
  have hb : b≤t := by unfold width at ht;nlinarith
  have hl : l≤t := by unfold width at ht;nlinarith
  have hn : n≤t := by unfold width at ht;nlinarith
  have ha : width b+(l+1)≤t := by nlinarith
  have hd := CompetitorDimensions.budget_bound b
  unfold CompetitorReusableDecision.capacity at hd
  rw [←Nat.mul_assoc] at hd
  have hd' := hd.trans (Nat.mul_le_mul_left (10*4096) (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2))
  have hp : WilliamsUnaryProduct.budget (width b+(l+1)) (n+1)≤10*t+6 := by
    unfold WilliamsUnaryProduct.budget
    nlinarith
  unfold CompetitorRecordScalarDrivers.budget
  change _≤50000*(t+1)^2
  nlinarith

theorem dimensions_bound (b l n : ℕ) : CompetitorRecordScalarDimensions.budget b l n≤
    100000*(CompetitorProducedScalar.commonWidth b l n+1)^2 := by
  have hd := driver_bound b l n
  have ht := CompetitorDimensions.budget_bound (CompetitorProducedScalar.commonWidth b l n)
  have hn := (CompetitorProducedScalar.common_width b l n).2.1
  unfold CompetitorReusableDecision.capacity at ht
  unfold CompetitorRecordScalarDimensions.budget RepairSource.ProjectionNormalization.Counter.budget
  nlinarith

theorem budget_bound (b l n : ℕ) : budget b l n≤
    221000*(n+1)*(CompetitorProducedScalar.commonWidth b l n+1)^2 := by
  have hd := dimensions_bound b l n
  have hs := CompetitorProducedScalar.budget_bound (CompetitorProducedScalar.commonWidth b l n) l n
    (CompetitorProducedScalar.common_width b l n).2.2
  have hm : (CompetitorProducedScalar.commonWidth b l n+1)^2≤
      (n+1)*(CompetitorProducedScalar.commonWidth b l n+1)^2 := by nlinarith
  have hm1 : 1≤(n+1)*(CompetitorProducedScalar.commonWidth b l n+1)^2 := by
    have h : 0<(n+1)*(CompetitorProducedScalar.commonWidth b l n+1)^2 := by positivity
    omega
  have hd' := hd.trans (Nat.mul_le_mul_left 100000 hm)
  unfold budget
  nlinarith only [hd',hs,hm1]

theorem polynomial_bound (b l n : ℕ) : budget b l n≤3536000*(n+1)^3*(b+l+1)^2 := by
  have hb := budget_bound b l n
  have hw : CompetitorProducedScalar.commonWidth b l n+1≤4*(n+1)*(b+l+1) := by
    rw [common_width_eq]
    unfold width
    nlinarith
  calc
    _ ≤ 221000*(n+1)*(CompetitorProducedScalar.commonWidth b l n+1)^2 := hb
    _ ≤ 221000*(n+1)*(4*(n+1)*(b+l+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)
    _ = _ := by ring

end NearCubicWires.RepairOrdinary.CompetitorRecordScalar

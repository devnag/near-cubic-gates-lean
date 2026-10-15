import Proof.Wire_3_5.RecoveryLedgerAt
import Proof.Wire_3_5.TransferTargets

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule
open Filter Topology

theorem oracleSize_ge (G q : ℕ) (hq : 1 ≤ q) : q ^ G ≤ RecoveryScheduleEnvelope.oracleSizeBound G q :=
  (Nat.pow_le_pow_right hq (RecoveryScheduleEnvelope.requiredDegree_le_oracleDegree G)).trans
    (PolynomialClock.pow_twoPow_le_pairClock _ q)

/-- **Case 1's size premises** at `G = 17c`. -/
theorem caseOne_size (c : ℕ) (hc : 1 ≤ c) (q n cap K : ℕ) (hK : K ≤ 50) (hq1 : 1 ≤ q)
    (hq : 12800 * (q + 1) ^ 16 ≤ q ^ 17) (hn : n + cap + 2 ≤ 4 * (q + 1) ^ 4) :
    K * (n + cap + 2) ^ 4 ≤ integerFloorRoot c (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q) := by
  apply le_integerFloorRoot (by omega)
  have h1 : K * (n + cap + 2) ^ 4 ≤ 50 * (4 * (q + 1) ^ 4) ^ 4 :=
    Nat.mul_le_mul hK (Nat.pow_le_pow_left hn 4)
  have h2 : 50 * (4 * (q + 1) ^ 4) ^ 4 = 12800 * (q + 1) ^ 16 := by ring
  have h3 : K * (n + cap + 2) ^ 4 ≤ q ^ 17 := by omega
  calc (K * (n + cap + 2) ^ 4) ^ c ≤ (q ^ 17) ^ c := Nat.pow_le_pow_left h3 c
    _ = q ^ (17 * c) := by rw [← pow_mul]
    _ ≤ RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q := oracleSize_ge _ q hq1

/-- `12800(q+1)^{16} ≤ q^{17}` eventually. -/
theorem eventually_12800 : ∀ᶠ q : ℕ in atTop, 12800 * (q + 1) ^ 16 ≤ q ^ 17 := by
  filter_upwards [eventually_ge_atTop (12800 * 2 ^ 16)] with q hq
  have h1 : (q + 1) ^ 16 ≤ (2 * q) ^ 16 := Nat.pow_le_pow_left (by omega) 16
  have h2 : (2 * q) ^ 16 = 2 ^ 16 * q ^ 16 := by ring
  have h3 : q ^ 17 = q * q ^ 16 := by ring
  calc 12800 * (q + 1) ^ 16 ≤ 12800 * (2 ^ 16 * q ^ 16) := Nat.mul_le_mul_left _ (h1.trans h2.le)
    _ = (12800 * 2 ^ 16) * q ^ 16 := by ring
    _ ≤ q * q ^ 16 := Nat.mul_le_mul_right _ hq
    _ = q ^ 17 := h3.symm

/-- **Case 1's advantage premise** eventually: `(q^{17c})^{−1/c} < e_{t(q)}`. -/
theorem eventually_caseOne_adv {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (c : ℕ) (hc : 1 ≤ c) :
    ∀ᶠ q : ℕ in atTop,
      Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) (-(1 : ℝ) / c) <
        xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := by
  filter_upwards [amplifier_le_eps_eventually ζ h0 h1 16 (by norm_num), eventually_ge_atTop 2] with q hq hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hX : ((q : ℝ) ^ (17 * c : ℕ)) ≤ (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) := by
    exact_mod_cast oracleSize_ge (17 * c) q (by omega)
  have hpos : (0 : ℝ) < (q : ℝ) ^ (17 * c : ℕ) := by positivity
  have hneg : -(1 : ℝ) / c ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / c := by positivity
    rw [neg_div]; linarith
  -- `X^{−1/c} ≤ (q^{17c})^{−1/c} = q^{−17}`
  have h1' : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) (-(1 : ℝ) / c) ≤
      Real.rpow ((q : ℝ) ^ (17 * c : ℕ)) (-(1 : ℝ) / c) :=
    Real.rpow_le_rpow_of_nonpos hpos hX hneg
  have h2 : Real.rpow ((q : ℝ) ^ (17 * c : ℕ)) (-(1 : ℝ) / c) = (q : ℝ) ^ (-(17 : ℝ)) := by
    show ((q : ℝ) ^ (17 * c : ℕ)) ^ (-(1 : ℝ) / c) = (q : ℝ) ^ (-(17 : ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    push_cast
    field_simp
  have h3 : (q : ℝ) ^ (-(17 : ℝ)) < (q : ℝ) ^ (-(16 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hq1 (by norm_num)
  have h4 : (q : ℝ) ^ (-(16 : ℝ)) ≤ xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := hq
  calc Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) q : ℝ) (-(1 : ℝ) / c)
      ≤ (q : ℝ) ^ (-(17 : ℝ)) := h1'.trans h2.le
    _ < (q : ℝ) ^ (-(16 : ℝ)) := h3
    _ ≤ xorEpsilon (ζ : ℝ) (rowBt h0 h1 q) := h4

end NearCubicWires.WireExponent3_5.Transfer

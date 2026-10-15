import Proof.Wire_3_5.RecoveryLedger

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.ComponentwiseCircuitRestriction NearCubicWires.RecoveryWitnessPolicy

section Caps
variable (Q m W : ℕ) (hQ : 1 ≤ Q) (hm : m + 1 ≤ 4 * Q) (hW : W + 1 ≤ 2 * Q ^ 4)

theorem natBitLength_mul_two_pow_le (a D : ℕ) (ha : 1 ≤ a) : natBitLength (a * 2 ^ D) ≤ D + a := by
  unfold natBitLength
  have h1 : a * 2 ^ D < 2 ^ (a + D) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self) (Nat.two_pow_pos D)
  have h2 : Nat.log 2 (a * 2 ^ D) < a + D := Nat.log_lt_of_lt_pow (by positivity) h1
  omega

include hm in
theorem ndc_le : normalizedGateDescriptionCap m ≤ 128 * Q ^ 3 := by
  unfold normalizedGateDescriptionCap
  have h1 : (m + 1) * (m * m + 1) + m ≤ 2 * (m + 1) ^ 3 := by nlinarith
  have h2 : (m + 1) ^ 3 ≤ (4 * Q) ^ 3 := Nat.pow_le_pow_left hm 3
  have h3 : (4 * Q) ^ 3 = 64 * Q ^ 3 := by ring
  omega

include hQ hm hW in
theorem symD_le : symmetricDescriptionCap m W ≤ 258 * Q ^ 7 := by
  unfold symmetricDescriptionCap
  have h1 := ndc_le Q m hm
  have hQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q hQ
  calc (W + 1) * (normalizedGateDescriptionCap m + 1) ≤ (2 * Q ^ 4) * (128 * Q ^ 3 + 1) :=
        Nat.mul_le_mul hW (by omega)
    _ ≤ (2 * Q ^ 4) * (129 * Q ^ 3) := Nat.mul_le_mul_left _ (by omega)
    _ = 258 * Q ^ 7 := by ring

include hQ hm in
theorem rgdc_le (D : ℕ) : restrictedGateDescriptionCap (Q - 1) m (2 ^ D) ≤ Q * (D + 4 * Q) + Q := by
  unfold restrictedGateDescriptionCap restrictedParameterBound
  have h := natBitLength_mul_two_pow_le (m + 1) D (by omega)
  have hQ1 : Q - 1 + 1 = Q := by omega
  rw [hQ1]
  have : natBitLength ((m + 1) * 2 ^ D) ≤ D + 4 * Q := by omega
  have h2 := Nat.mul_le_mul_left Q this
  omega

include hQ hm hW in
/-- **The `SYM∘THR` restricted description cap** is at most `528(q+1)^{12}`. -/
theorem symLdesc_le :
    restrictedSymmetricDescriptionCap (Q - 1) m (2 ^ symmetricDescriptionCap m W) W ≤ 528 * Q ^ 12 := by
  unfold restrictedSymmetricDescriptionCap
  have hD := symD_le Q m W hQ hm hW
  have hr := rgdc_le Q m hQ hm (symmetricDescriptionCap m W)
  have hQ1 : Q ≤ Q ^ 8 := Nat.le_self_pow (by norm_num) Q
  have hQ7 : Q * Q ≤ Q ^ 8 := by
    calc Q * Q = Q ^ 2 := by ring
      _ ≤ Q ^ 8 := Nat.pow_le_pow_right hQ (by norm_num)
  have h8 : Q * (symmetricDescriptionCap m W + 4 * Q) + Q + 1 ≤ 264 * Q ^ 8 := by
    have e : Q * (258 * Q ^ 7) = 258 * Q ^ 8 := by ring
    have h1 : Q * (symmetricDescriptionCap m W + 4 * Q) ≤ Q * (258 * Q ^ 7 + 4 * Q) :=
      Nat.mul_le_mul_left Q (by omega)
    have h2 : Q * (258 * Q ^ 7 + 4 * Q) = 258 * Q ^ 8 + 4 * (Q * Q) := by ring
    have h3 : 1 ≤ Q ^ 8 := Nat.one_le_pow 8 Q hQ
    omega
  calc (W + 1) * (restrictedGateDescriptionCap (Q - 1) m (2 ^ symmetricDescriptionCap m W) + 1)
      ≤ (2 * Q ^ 4) * (264 * Q ^ 8) := Nat.mul_le_mul hW (by omega)
    _ = 528 * Q ^ 12 := by ring

include hQ hm hW in
theorem thrD_le : thresholdDescriptionCap m W ≤ 272 * Q ^ 12 := by
  unfold thresholdDescriptionCap
  have hn := ndc_le Q m hm
  have hwc : normalizedGateDescriptionCap W ≤ 16 * Q ^ 12 := by
    unfold normalizedGateDescriptionCap
    have h1 : (W + 1) * (W * W + 1) + W ≤ 2 * (W + 1) ^ 3 := by nlinarith
    have h2 : (W + 1) ^ 3 ≤ (2 * Q ^ 4) ^ 3 := Nat.pow_le_pow_left hW 3
    have h3 : (2 * Q ^ 4) ^ 3 = 8 * Q ^ 12 := by ring
    omega
  have hWn : W * normalizedGateDescriptionCap m ≤ 256 * Q ^ 12 := by
    have hW' : W ≤ 2 * Q ^ 4 := by omega
    have h7 : Q ^ 7 ≤ Q ^ 12 := Nat.pow_le_pow_right hQ (by norm_num)
    calc W * normalizedGateDescriptionCap m ≤ (2 * Q ^ 4) * (128 * Q ^ 3) := Nat.mul_le_mul hW' hn
      _ = 256 * Q ^ 7 := by ring
      _ ≤ 256 * Q ^ 12 := Nat.mul_le_mul_left _ h7
  omega

include hQ hm hW in
/-- **The `THR∘THR` restricted description cap** is at most `75894(q+1)^{25}`. -/
theorem thrLdesc_le :
    restrictedThresholdDescriptionCap (Q - 1) m (2 ^ thresholdDescriptionCap m W) (thresholdDescriptionCap m W) ≤
      75894 * Q ^ 25 := by
  unfold restrictedThresholdDescriptionCap
  have hD := thrD_le Q m W hQ hm hW
  have hr := rgdc_le Q m hQ hm (thresholdDescriptionCap m W)
  have h12 : 1 ≤ Q ^ 12 := Nat.one_le_pow 12 Q hQ
  have h13 : 1 ≤ Q ^ 13 := Nat.one_le_pow 13 Q hQ
  have hQQ : Q * Q ≤ Q ^ 13 := by
    calc Q * Q = Q ^ 2 := by ring
      _ ≤ Q ^ 13 := Nat.pow_le_pow_right hQ (by norm_num)
  have hQ1 : Q ≤ Q ^ 13 := Nat.le_self_pow (by norm_num) Q
  have hg : Q * (thresholdDescriptionCap m W + 4 * Q) + Q + 1 ≤ 278 * Q ^ 13 := by
    have h1 : Q * (thresholdDescriptionCap m W + 4 * Q) ≤ Q * (272 * Q ^ 12 + 4 * Q) :=
      Nat.mul_le_mul_left Q (by omega)
    have h2 : Q * (272 * Q ^ 12 + 4 * Q) = 272 * Q ^ 13 + 4 * (Q * Q) := by ring
    omega
  calc (thresholdDescriptionCap m W + 1) *
        (restrictedGateDescriptionCap (Q - 1) m (2 ^ thresholdDescriptionCap m W) + 1)
      ≤ (273 * Q ^ 12) * (278 * Q ^ 13) := Nat.mul_le_mul (by omega) (by omega)
    _ = 75894 * Q ^ 25 := by ring

end Caps

end NearCubicWires.WireExponent3_5.Transfer

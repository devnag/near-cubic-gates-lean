import Proof.Gates.Dispatch.ParamsG

set_option autoImplicit false

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

/-- A polynomial bound below a power of two. -/
theorem pw {x B d c W : ℕ} (hx : x ≤ c * B ^ d) (hW : c + d * B ≤ W) : x < 2 ^ W := by
  have h1 : B ^ d ≤ 2 ^ (d * B) := by
    calc B ^ d ≤ (2 ^ B) ^ d := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le d
      _ = 2 ^ (d * B) := by rw [← pow_mul, mul_comm]
  have h2 : c < 2 ^ c := Nat.lt_two_pow_self
  calc x ≤ c * B ^ d := hx
    _ ≤ c * 2 ^ (d * B) := Nat.mul_le_mul_left _ h1
    _ < 2 ^ c * 2 ^ (d * B) := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
    _ = 2 ^ (c + d * B) := by rw [pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW

theorem pow_mono_B {x B : ℕ} (hx : x ≤ B) (d : ℕ) : x ^ d ≤ B ^ d := Nat.pow_le_pow_left hx d

theorem B_pows (B : ℕ) (hB : 1 ≤ B) : B ≤ B ^ 2 ∧ B ^ 2 ≤ B ^ 3 ∧ B ^ 3 ≤ B ^ 4 ∧ B ^ 4 ≤ B ^ 8 ∧ 1 ≤ B ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ 2 := Nat.pow_le_pow_right hB (by norm_num)
  · exact Nat.pow_le_pow_right hB (by norm_num)
  · exact Nat.pow_le_pow_right hB (by norm_num)
  · exact Nat.pow_le_pow_right hB (by norm_num)
  · exact Nat.one_le_pow _ _ (by omega)

/-- `T ≥ 1` (indeed `2^T ≥ 64`): `β ≤ 1/16` while `4 J_max 2^k ≥ 4`. -/
theorem T_pos (k J : ℕ) (β : ℚ) (T : ℕ) (hJ : 1 ≤ J) (hβ : β ≤ 1 / 16) (h : TPass k J β T) : 1 ≤ T := by
  rcases Nat.eq_zero_or_pos T with h0 | h0
  · exfalso
    unfold TPass at h
    rw [h0, pow_zero, one_mul] at h
    have : (4 : ℚ) ≤ ((4 * J * 2 ^ k : ℕ) : ℚ) := by
      have : 4 ≤ 4 * J * 2 ^ k := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        nlinarith
      exact_mod_cast this
    linarith
  · exact h0

theorem window_le (P : ℕ) : ScalarWindow.window (dyadicPrimes P) ≤ (P + 1) * (P + 1) := by
  unfold ScalarWindow.window
  have hc : (dyadicPrimes P).card ≤ P + 1 := by
    rw [dyadicPrimes_eq]; exact le_trans (Finset.card_filter_le _ _) (by simp)
  have hs := sum_le_mul (dyadicPrimes P) P (fun p hp => ((mem_dyadicPrimes P p).1 hp).1)
  have : (dyadicPrimes P).card * P ≤ (P + 1) * P := Nat.mul_le_mul_right _ hc
  nlinarith

theorem pairSide_le (D : ℕ) (hD : 1 ≤ D) : pairSide D ≤ D := by
  unfold pairSide
  split_ifs
  · exact hD
  · exact Nat.findGreatest_le _

theorem windowInUse_le (pr : Bool) (L2 D : ℕ) (h : L2 ≤ D) : windowInUse pr L2 D ≤ D := by
  unfold windowInUse; split_ifs <;> omega

theorem window_pos (P : ℕ) : 1 ≤ ScalarWindow.window (dyadicPrimes P) := by
  unfold ScalarWindow.window; omega

theorem sqrt_hE_le (P : ℕ) : Nat.sqrt (2 * (P / 4) ^ 2) ≤ P := by
  have : Nat.sqrt (2 * (P / 4) ^ 2) ≤ 2 * (P / 4) := by
    calc Nat.sqrt (2 * (P / 4) ^ 2) ≤ Nat.sqrt ((2 * (P / 4)) ^ 2) := Nat.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (P / 4) := Nat.sqrt_eq' _
  omega

end NearCubicGates.Close.Dispatch

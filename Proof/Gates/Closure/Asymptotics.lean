import Proof.Gates.Closure.Supply
import Proof.Gates.Counter.Eventual
import Proof.Gates.Transfer.Budget

set_option autoImplicit false

namespace NearCubicGates.Close.Closure

open NearCubicGates NearCubicGates.Target NearCubicGates.Close.Interfaces NearCubicGates.Close.Transfer

/-- `K λ(q)^d < q` for all large `q`. -/
theorem lambda_poly_lt (K d : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧ ∀ q, onset ≤ q → K * lambda q ^ d < q := by
  obtain ⟨onset, hon, h⟩ := NearCubicGates.Close.Counter.polynomial_lambda_binary K d
  refine ⟨onset, by omega, fun q hq => ?_⟩
  obtain ⟨h16, hK⟩ := h q hq
  have hq1 : 1 < q := by omega
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hq1
  have hexp : lambda q / 4 ≤ (Nat.clog 2 q).pred := by
    rw [Nat.pred_eq_sub_one]; unfold lambda at h16 ⊢; omega
  calc K * lambda q ^ d ≤ 2 ^ (lambda q / 4) := hK
    _ ≤ 2 ^ (Nat.clog 2 q).pred := Nat.pow_le_pow_right (by norm_num) hexp
    _ < q := hlt

theorem mu_le_lambda (q : ℕ) : mu q ≤ lambda q := NearCubicGates.Close.Counter.clog_le_self _

theorem asymptoticsFacts : AsymptoticsFacts := by
  -- common positivity at `q ≥ 4`
  have hpos : ∀ q, 4 ≤ q → (1 : ℝ) ≤ (lambda q : ℝ) ∧ (1 : ℝ) ≤ (mu q : ℝ) ∧ (mu q : ℝ) ≤ (lambda q : ℝ) := by
    intro q hq
    refine ⟨?_, ?_, ?_⟩
    · have := lambda_ge_two hq; exact_mod_cast (by omega : 1 ≤ lambda q)
    · exact_mod_cast mu_ge_one hq
    · exact_mod_cast mu_le_lambda q
  -- the denominator of `𝒜₃` is at most `λ¹³`
  have hden : ∀ q, 4 ≤ q → (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 ≤ (lambda q : ℝ) ^ 13 := by
    intro q hq
    obtain ⟨hL, hM, hML⟩ := hpos q hq
    have h1 : (lambda q : ℝ) ^ ((21 : ℝ) / 4) ≤ (lambda q : ℝ) ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    have h2 : (mu q : ℝ) ^ 7 ≤ (lambda q : ℝ) ^ 7 := pow_le_pow_left₀ (by linarith) hML 7
    calc (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 ≤ (lambda q : ℝ) ^ (6 : ℕ) * (lambda q : ℝ) ^ 7 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (lambda q : ℝ) ^ 13 := by ring
  have hdenpos : ∀ q, 4 ≤ q → 0 < (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 := by
    intro q hq
    obtain ⟨hL, hM, -⟩ := hpos q hq
    have : 0 < (lambda q : ℝ) ^ ((21 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  refine ⟨?_, ?_⟩
  · -- `𝒜₃ → ∞`
    intro M
    obtain ⟨on, hon4, hon⟩ := lambda_poly_lt (Nat.ceil M + 1) 13
    refine ⟨on, fun q hq => ?_⟩
    have hq4 : 4 ≤ q := hon4.trans hq
    obtain ⟨hL, -, -⟩ := hpos q hq4
    have hK : ((Nat.ceil M + 1 : ℕ) : ℝ) * (lambda q : ℝ) ^ 13 < (q : ℝ) := by exact_mod_cast hon q hq
    have hQ1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hL13 : 0 < (lambda q : ℝ) ^ 13 := by positivity
    have hA : (q : ℝ) ^ 3 / (lambda q : ℝ) ^ 13 ≤ A3 q := by
      unfold A3
      exact div_le_div_of_nonneg_left (by positivity) (hdenpos q hq4) (hden q hq4)
    have hM : M ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil M]
    have hge : ((Nat.ceil M + 1 : ℕ) : ℝ) ≤ (q : ℝ) ^ 3 / (lambda q : ℝ) ^ 13 := by
      rw [le_div_iff₀ hL13]
      have hq3 : (q : ℝ) ≤ (q : ℝ) ^ 3 := le_self_pow₀ hQ1 (by norm_num)
      linarith
    linarith
  · -- eventually `0 ≤ 𝒜₃ ≤ q³` and `𝒜₃ ≤ 𝒜₁`
    obtain ⟨on, hon4, hon⟩ := lambda_poly_lt 1 4
    refine ⟨on, fun q hq => ?_⟩
    have hq4 : 4 ≤ q := hon4.trans hq
    obtain ⟨hL, hM, hML⟩ := hpos q hq4
    have hD := hdenpos q hq4
    have hQ0 : (0 : ℝ) ≤ q := by positivity
    refine ⟨by unfold A3; positivity, ?_, ?_⟩
    · unfold A3
      rw [div_le_iff₀ hD]
      have hD1 : 1 ≤ (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 := by
        have h1 : 1 ≤ (lambda q : ℝ) ^ ((21 : ℝ) / 4) := Real.one_le_rpow hL (by norm_num)
        have h2 : 1 ≤ (mu q : ℝ) ^ 7 := one_le_pow₀ hM
        nlinarith
      have : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
      nlinarith
    · -- `λ^{3/4} μ ≤ λ² ≤ √q`
      have h4 : (lambda q : ℝ) ^ 4 < (q : ℝ) := by
        have := hon q hq; rw [one_mul] at this; exact_mod_cast this
      have hsq : (lambda q : ℝ) ^ 2 ≤ (q : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow]
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have h34 : (lambda q : ℝ) ^ ((3 : ℝ) / 4) ≤ (lambda q : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hL (show (3 : ℝ) / 4 ≤ 1 by norm_num)
        rwa [Real.rpow_one] at this
      have hkey : (lambda q : ℝ) ^ ((3 : ℝ) / 4) * (mu q : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 2) := by
        have : (lambda q : ℝ) ^ ((3 : ℝ) / 4) * (mu q : ℝ) ≤ (lambda q : ℝ) * (lambda q : ℝ) :=
          mul_le_mul h34 hML (by linarith) (by linarith)
        nlinarith
      have hLpos : (0 : ℝ) < (lambda q : ℝ) := by linarith
      have hsplitL : (lambda q : ℝ) ^ (6 : ℕ) =
          (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (lambda q : ℝ) ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hLpos, ← Real.rpow_natCast]; norm_num
      have hsplitQ : (q : ℝ) ^ ((7 : ℝ) / 2) = (q : ℝ) ^ (3 : ℕ) * (q : ℝ) ^ ((1 : ℝ) / 2) := by
        have hQpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        rw [← Real.rpow_natCast, ← Real.rpow_add hQpos]; norm_num
      unfold A3 A1
      have hD1 : 0 < (lambda q : ℝ) ^ 6 * (mu q : ℝ) ^ 8 := by positivity
      rw [div_le_div_iff₀ hD hD1, hsplitQ, hsplitL]
      have hr0 : 0 ≤ (q : ℝ) ^ (3 : ℕ) * (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 := by
        have : 0 ≤ (lambda q : ℝ) ^ ((21 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
        positivity
      have := mul_le_mul_of_nonneg_left hkey hr0
      calc (q : ℝ) ^ 3 * ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (lambda q : ℝ) ^ ((3 : ℝ) / 4) * (mu q : ℝ) ^ 8)
          = (q : ℝ) ^ (3 : ℕ) * (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 *
              ((lambda q : ℝ) ^ ((3 : ℝ) / 4) * (mu q : ℝ)) := by ring
        _ ≤ (q : ℝ) ^ (3 : ℕ) * (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 * (q : ℝ) ^ ((1 : ℝ) / 2) := this
        _ = (q : ℝ) ^ (3 : ℕ) * (q : ℝ) ^ ((1 : ℝ) / 2) * ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7) := by
            ring

end NearCubicGates.Close.Closure

import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open Filter Topology

def Lg (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

theorem Lg_tendsto : Tendsto Lg atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun n hn => ?_⟩
  have h1 : b ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  exact h1.trans (Nat.log_le_clog 2 (n + 2))

theorem logpow_mul_rpow_neg_tendsto (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.log (Lg n) ^ a * ((Lg n : ℕ) : ℝ) ^ (-b)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ a / x ^ b) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero
  have h1' : Tendsto (fun x : ℝ => Real.log x ^ a * x ^ (-b)) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have h2 : Tendsto (fun n : ℕ => ((Lg n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Lg_tendsto
  exact h1'.comp h2

theorem rowB_load_factor_tendsto :
    Tendsto (fun n : ℕ => Real.log (Lg n) ^ ((11 : ℝ) / 4) * ((Lg n : ℕ) : ℝ) ^ (-((1 : ℝ) / 32)))
      atTop (𝓝 0) :=
  logpow_mul_rpow_neg_tendsto _ (by norm_num)

def LgRatioTendsOne : Prop :=
  ∀ (C : ℕ) (q n : ℕ → ℕ), Tendsto q atTop atTop → (∀ i, q i ≤ n i ∧ n i ≤ q i * Lg (q i) ^ C) →
    Tendsto (fun i => (Lg (n i) : ℝ) / Lg (q i)) atTop (𝓝 1)

def AdvantageEventually : Prop :=
  ∀ (c τ K : ℝ), 0 < c → c < τ → 0 < K → ∀ (C : ℕ) (q n : ℕ → ℕ), Tendsto q atTop atTop →
    (∀ i, q i ≤ n i ∧ n i ≤ q i * Lg (q i) ^ C) →
    ∀ᶠ i in atTop, K * (Lg (q i) : ℝ) ^ (-τ) < (Lg (n i) : ℝ) ^ (-c)

def SavingBeatsPoly : Prop :=
  ∀ (A B : ℕ) (k : ℕ → ℕ), Tendsto (fun q => (k q : ℝ) / Lg q) atTop atTop →
    Tendsto (fun q : ℕ => (q : ℝ) ^ (A + B) / (2 : ℝ) ^ ((k q : ℝ) / 4)) atTop (𝓝 0)

theorem rowB_load_exponents :
    ((5 : ℚ) + 2 * (3 / 16) - 87 / 16) / 2 = -1 / 32 ∧ ((4 : ℚ) + 2 * (3 / 16) - 71 / 16) / 2 = -1 / 32 := by
  norm_num

theorem rowB_cap_reserves : (11 / 2 : ℚ) - 87 / 16 = 1 / 16 ∧ (9 / 2 : ℚ) - 71 / 16 = 1 / 16 := by norm_num

theorem rowB_parameter_order :
    (1 / 8 : ℚ) < 3 / 16 ∧ (5 : ℚ) + 2 * (3 / 16) < 87 / 16 ∧ (87 / 16 : ℚ) < 11 / 2 ∧
      (4 : ℚ) + 2 * (3 / 16) < 71 / 16 ∧ (71 / 16 : ℚ) < 9 / 2 ∧
      (11 / 2 : ℚ) > 5 + 2 * (1 / 8) ∧ (9 / 2 : ℚ) > 4 + 2 * (1 / 8) := by
  norm_num

/-! ## Numeric constants checked by computation (Appendix D §2), proved -/

theorem filtGap_constants :
    (15 / 32 : ℚ) * (64 / 65) > 46 / 100 ∧ (1 / 32 : ℚ) / 2 = 1 / 64 ∧ (1 / (64 : ℚ)) * 4096 = 64 := by
  norm_num

theorem filtGap_walk (m : ℕ) :
    (2 : ℚ) ^ (2 * m + 1) * (1 / 128) * (1 / 128 + 1 / 128) ^ m = 1 / 2 ^ (2 * (2 * m + 1) + 4) := by
  rw [show (1 / 128 + 1 / 128 : ℚ) = 1 / 2 ^ 6 by norm_num, show (1 / 128 : ℚ) = 1 / 2 ^ 7 by norm_num]
  rw [div_pow, one_pow, ← pow_mul]
  field_simp
  ring

theorem sampRoot_constants (N h η F : ℝ) (hN : 0 < N) (hh : 0 < h) (hη : 0 < η) (hη1 : η ≤ 1) (hF : 1 ≤ F) :
    let Q := 1024 * N * h * η⁻¹ ^ 2 * F ^ 2
    F * (2 * Real.sqrt (N * h / Q)) = η / 16 ∧ F * (16 * N * h / (3 * Q)) ≤ η / 192 := by
  intro Q
  have hF0 : 0 < F := lt_of_lt_of_le one_pos hF
  have hQ : N * h / Q = (η / (32 * F)) ^ 2 := by
    simp only [Q]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hQ, Real.sqrt_sq (by positivity)]; field_simp; ring
  · have : F * (16 * N * h / (3 * Q)) = η ^ 2 / (192 * F) := by simp only [Q]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_le_mul_of_nonneg_left hF hη.le]

theorem trSparse_constant (s : ℕ) (hs : 1 ≤ s) :
    (16 * s + 3 * s * (s - 1) : ℝ) ≤ 19 * (s : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  nlinarith

end NearCubicWires.WireExponent3_5.Shared

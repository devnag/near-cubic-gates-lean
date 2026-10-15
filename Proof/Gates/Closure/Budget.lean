import Proof.Gates.Interfaces.Counter
import Proof.Gates.Transfer.Budget

/-!
# The computable weight budget — paper v2 line 2516 ("b(q) = ⌊η₀ ε 𝒜₃(q)⌋")

The worker checks `topWeight ≤ b(q)`, so `b` must be computable from `q` with integer arithmetic. With a rational
`η > 0` and `r = ⌈λ^{1/4}⌉` (`root4 λ`, the least `r` with `λ ≤ r⁴`):
`b(q) = ⌊η q³ / (λ⁵ r μ⁷)⌋`. Since `λ^{21/4} ≤ λ⁵ r ≤ 2 λ^{21/4}`, `η𝒜₃(q)/2 − 1 ≤ b(q) ≤ η𝒜₃(q)`: the paper's
`b(q) = ⌊η₀ ε 𝒜₃(q)⌋` up to the constant factor 2, which is all the transfer and the counter use.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Closure

open NearCubicGates NearCubicGates.Target NearCubicGates.Close.Interfaces NearCubicGates.Close.Transfer

/-- `⌈n^{1/4}⌉`: the least `r` with `n ≤ r⁴`. -/
def root4 (n : ℕ) : ℕ := Nat.find (⟨n, by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ 4 := Nat.pow_le_pow_right h (by norm_num)⟩ : ∃ r : ℕ, n ≤ r ^ 4)

theorem le_root4_pow (n : ℕ) : n ≤ root4 n ^ 4 := Nat.find_spec (p := fun r => n ≤ r ^ 4) _

theorem root4_pred_lt (n : ℕ) (h : 1 ≤ root4 n) : (root4 n - 1) ^ 4 < n := by
  have hmin := Nat.find_min (p := fun r => n ≤ r ^ 4) (m := root4 n - 1) _ (by unfold root4 at h ⊢; omega)
  simpa using hmin

/-- The weight budget at rational scale `η`. -/
def budgetOf (η : ℚ) (q : ℕ) : ℕ :=
  (η.num.toNat * q ^ 3) / (η.den * (lambda q ^ 5 * root4 (lambda q) * mu q ^ 7))

/-- `λ^{1/4} ≤ ⌈λ^{1/4}⌉ ≤ 2 λ^{1/4}` for `λ ≥ 1`. -/
theorem root4_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (root4 n : ℝ) ∧ (root4 n : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hr : 1 ≤ root4 n := by
    by_contra h0
    have : root4 n = 0 := by omega
    have := le_root4_pow n
    rw [‹root4 n = 0›] at this
    simp at this; omega
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h4 : ∀ y : ℝ, 0 ≤ y → (y ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = y := by
    intro y hy
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  have hroot1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  constructor
  · have hle : (n : ℝ) ≤ ((root4 n : ℕ) : ℝ) ^ (4 : ℕ) := by exact_mod_cast le_root4_pow n
    have := Real.rpow_le_rpow hn0 hle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [h4 _ (by positivity)] at this
  · have hlt : (((root4 n - 1 : ℕ) : ℝ)) ^ (4 : ℕ) < (n : ℝ) := by exact_mod_cast root4_pred_lt n hr
    have := Real.rpow_lt_rpow (by positivity) hlt (by norm_num : (0 : ℝ) < 1 / 4)
    rw [h4 _ (by positivity)] at this
    have hc : ((root4 n - 1 : ℕ) : ℝ) = (root4 n : ℝ) - 1 := by push_cast [Nat.cast_sub hr]; ring
    rw [hc] at this
    linarith

/-- `λ^{21/4} ≤ λ⁵ ⌈λ^{1/4}⌉ ≤ 2 λ^{21/4}`. -/
theorem lambda_root_bounds (q : ℕ) (hq : 4 ≤ q) :
    (lambda q : ℝ) ^ ((21 : ℝ) / 4) ≤ (lambda q : ℝ) ^ 5 * (root4 (lambda q) : ℝ) ∧
      (lambda q : ℝ) ^ 5 * (root4 (lambda q) : ℝ) ≤ 2 * (lambda q : ℝ) ^ ((21 : ℝ) / 4) := by
  have hL : 1 ≤ lambda q := by have := lambda_ge_two hq; omega
  obtain ⟨h1, h2⟩ := root4_bounds (lambda q) hL
  have hLpos : (0 : ℝ) < lambda q := by exact_mod_cast (by omega : 0 < lambda q)
  have hsplit : (lambda q : ℝ) ^ ((21 : ℝ) / 4) = (lambda q : ℝ) ^ 5 * (lambda q : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]; norm_num
  have h5 : (0 : ℝ) ≤ (lambda q : ℝ) ^ 5 := by positivity
  rw [hsplit]
  constructor
  · exact mul_le_mul_of_nonneg_left h1 h5
  · nlinarith [mul_le_mul_of_nonneg_left h2 h5]

/-- `η𝒜₃(q)/2 − 1 ≤ b(q) ≤ η𝒜₃(q)` for `q ≥ 4`, `η > 0`. -/
theorem budgetOf_bounds (η : ℚ) (hη : 0 < η) (q : ℕ) (hq : 4 ≤ q) :
    (budgetOf η q : ℝ) ≤ (η : ℝ) * A3 q ∧ (η : ℝ) * A3 q / 2 - 1 ≤ (budgetOf η q : ℝ) := by
  obtain ⟨hlo, hhi⟩ := lambda_root_bounds q hq
  have hL : 2 ≤ lambda q := lambda_ge_two hq
  have hM : 1 ≤ mu q := mu_ge_one hq
  have hr : 1 ≤ root4 (lambda q) := by
    have := (root4_bounds (lambda q) (by omega)).1
    have h1 : (1 : ℝ) ≤ (lambda q : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ lambda q))
      (by norm_num)
    have : (1 : ℝ) ≤ root4 (lambda q) := by linarith
    exact_mod_cast this
  set D : ℕ := lambda q ^ 5 * root4 (lambda q) * mu q ^ 7 with hD
  have hDpos : 0 < D := by positivity
  have hnum : ((η.num.toNat : ℕ) : ℝ) = (η.num : ℝ) := by
    have : 0 ≤ η.num := Rat.num_nonneg.2 hη.le
    exact_mod_cast Int.toNat_of_nonneg this
  have hη' : (η : ℝ) = (η.num : ℝ) / (η.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (0 : ℝ) < η.den := by exact_mod_cast η.den_pos
  -- the exact quotient `X = η q³ / D`
  set X : ℝ := (η : ℝ) * (q : ℝ) ^ 3 / (D : ℝ) with hX
  have hfloor : (budgetOf η q : ℝ) ≤ X ∧ X - 1 < (budgetOf η q : ℝ) := by
    have hden' : 0 < η.den * D := Nat.mul_pos η.den_pos hDpos
    have hq1 := Nat.div_mul_le_self (η.num.toNat * q ^ 3) (η.den * D)
    have hq2 := Nat.lt_div_mul_add (a := η.num.toNat * q ^ 3) hden'
    unfold budgetOf
    rw [← hD]
    have hXe : X = ((η.num.toNat * q ^ 3 : ℕ) : ℝ) / ((η.den * D : ℕ) : ℝ) := by
      rw [hX, hη']; push_cast; rw [hnum]; field_simp
    rw [hXe]
    have hpos : (0 : ℝ) < ((η.den * D : ℕ) : ℝ) := by exact_mod_cast hden'
    constructor
    · rw [le_div_iff₀ hpos]; exact_mod_cast hq1
    · rw [div_sub_one hpos.ne', div_lt_iff₀ hpos]
      have : ((η.num.toNat * q ^ 3 : ℕ) : ℝ) < ((η.num.toNat * q ^ 3 / (η.den * D) * (η.den * D) + η.den * D : ℕ) : ℝ) := by
        exact_mod_cast hq2
      push_cast at this ⊢; linarith
  have hDr : (D : ℝ) = (lambda q : ℝ) ^ 5 * (root4 (lambda q) : ℝ) * (mu q : ℝ) ^ 7 := by rw [hD]; push_cast; ring
  have hμ : (0 : ℝ) < (mu q : ℝ) ^ 7 := by positivity
  have hA3 : A3 q = (q : ℝ) ^ 3 / ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7) := rfl
  have hLr : (0 : ℝ) < (lambda q : ℝ) ^ ((21 : ℝ) / 4) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < lambda q)) _
  have hηq : (0 : ℝ) ≤ (η : ℝ) * (q : ℝ) ^ 3 := by positivity
  constructor
  · -- `X ≤ η𝒜₃`: the denominator `D ≥ λ^{21/4} μ⁷`
    refine hfloor.1.trans ?_
    rw [hX, hA3, mul_div_assoc', hDr]
    apply div_le_div_of_nonneg_left hηq (by positivity)
    exact mul_le_mul_of_nonneg_right hlo hμ.le
  · -- `X ≥ η𝒜₃/2`: the denominator `D ≤ 2 λ^{21/4} μ⁷`
    have hX2 : (η : ℝ) * A3 q / 2 ≤ X := by
      rw [hX, hA3, hDr, div_le_div_iff₀ (by norm_num) (by positivity)]
      have hb : (lambda q : ℝ) ^ 5 * (root4 (lambda q) : ℝ) * (mu q : ℝ) ^ 7 ≤
          2 * ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7) := by nlinarith [mul_le_mul_of_nonneg_right hhi hμ.le]
      have hE : (0 : ℝ) < (lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7 := mul_pos hLr hμ
      have hc : (0 : ℝ) ≤ (η : ℝ) * ((q : ℝ) ^ 3 / ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7)) := by
        positivity
      calc (η : ℝ) * ((q : ℝ) ^ 3 / ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7)) *
            ((lambda q : ℝ) ^ 5 * (root4 (lambda q) : ℝ) * (mu q : ℝ) ^ 7)
          ≤ (η : ℝ) * ((q : ℝ) ^ 3 / ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7)) *
            (2 * ((lambda q : ℝ) ^ ((21 : ℝ) / 4) * (mu q : ℝ) ^ 7)) := mul_le_mul_of_nonneg_left hb hc
        _ = (η : ℝ) * (q : ℝ) ^ 3 * 2 := by field_simp
    linarith [hfloor.2]

end NearCubicGates.Close.Closure

import Mathlib

/-!
# A04: the dyadic accuracy `δ = 2^(-k-2)` and `ε/8 < δ ≤ ε/4`

 ("Full-range amplification interface"): "In the remaining regime `n^c < S = S(n) < U(n)`, put
`ε = S^{-1/c}`. Compute the least integer `k` such that `2^{ck} ≥ S`, and use the dyadic accuracy `δ = 2^{-k-2}`;
then `ε/8 < δ ≤ ε/4`. All parameter choices use integer arithmetic."

`dyadicExp c S` is that least `k` (an integer computation); `dyadicAcc k = 2^(-k-2)`. The two inequalities are
`dyadicAcc_le` and `lt_dyadicAcc`, for every integer `c ≥ 1` and every `S ≥ 2` (the middle regime has
`S > n^c ≥ 2^c ≥ 2`). The exponent `ε = S^{-1/c}` is written exactly as in the target
(`(S : ℝ) ^ (-(1 : ℝ) / c)`, `Statement.lean:1013`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

theorem exists_le_two_pow_mul (c S : ℕ) (hc : 1 ≤ c) : ∃ k, S ≤ 2 ^ (c * k) :=
  ⟨S, (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left S hc))⟩

/-- `app:sources`, "Full-range amplification interface": "the least integer `k` such that `2^{ck} ≥ S`". -/
def dyadicExp (c S : ℕ) (hc : 1 ≤ c) : ℕ := Nat.find (exists_le_two_pow_mul c S hc)

theorem le_two_pow_dyadicExp (c S : ℕ) (hc : 1 ≤ c) : S ≤ 2 ^ (c * dyadicExp c S hc) :=
  Nat.find_spec (exists_le_two_pow_mul c S hc)

theorem two_pow_lt_of_lt_dyadicExp (c S : ℕ) (hc : 1 ≤ c) (j : ℕ) (hj : j < dyadicExp c S hc) :
    2 ^ (c * j) < S := by
  have := Nat.find_min (exists_le_two_pow_mul c S hc) hj
  omega

theorem one_le_dyadicExp (c S : ℕ) (hc : 1 ≤ c) (hS : 2 ≤ S) : 1 ≤ dyadicExp c S hc := by
  by_contra h
  have h0 : dyadicExp c S hc = 0 := by omega
  have := le_two_pow_dyadicExp c S hc
  rw [h0, Nat.mul_zero, pow_zero] at this
  omega

/-- `2^(c(k-1)) < S` for the least `k` (strict, below the least exponent). -/
theorem two_pow_pred_lt (c S : ℕ) (hc : 1 ≤ c) (hS : 2 ≤ S) :
    2 ^ (c * (dyadicExp c S hc - 1)) < S :=
  two_pow_lt_of_lt_dyadicExp c S hc _ (by have := one_le_dyadicExp c S hc hS; omega)

/-- The dyadic accuracy `δ = 2^(-k-2)`. -/
noncomputable def dyadicAcc (k : ℕ) : ℝ := 1 / 2 ^ (k + 2)

theorem dyadicAcc_pos (k : ℕ) : 0 < dyadicAcc k := by unfold dyadicAcc; positivity

/-- `(S : ℝ)^(1/c) ≤ 2^k` when `S ≤ 2^(c k)`. -/
theorem rpow_inv_le_of_le (c S k : ℕ) (hc : 1 ≤ c) (h : S ≤ 2 ^ (c * k)) :
    (S : ℝ) ^ ((1 : ℝ) / c) ≤ 2 ^ k := by
  have h1 : (S : ℝ) ≤ ((2 : ℝ) ^ k) ^ c := by
    rw [← pow_mul, mul_comm]; exact_mod_cast h
  calc (S : ℝ) ^ ((1 : ℝ) / c) ≤ (((2 : ℝ) ^ k) ^ c) ^ ((1 : ℝ) / c) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = 2 ^ k := by
        rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by exact_mod_cast (show c ≠ 0 by omega))]

/-- `2^j < (S : ℝ)^(1/c)` when `2^(c j) < S`. -/
theorem lt_rpow_inv_of_lt (c S j : ℕ) (hc : 1 ≤ c) (h : 2 ^ (c * j) < S) :
    (2 : ℝ) ^ j < (S : ℝ) ^ ((1 : ℝ) / c) := by
  have h1 : ((2 : ℝ) ^ j) ^ c < (S : ℝ) := by
    rw [← pow_mul, mul_comm]; exact_mod_cast h
  have hcpos : (0 : ℝ) < 1 / c := by
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    positivity
  calc (2 : ℝ) ^ j = (((2 : ℝ) ^ j) ^ c) ^ ((1 : ℝ) / c) := by
        rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by exact_mod_cast (show c ≠ 0 by omega))]
    _ < (S : ℝ) ^ ((1 : ℝ) / c) := Real.rpow_lt_rpow (by positivity) h1 hcpos

theorem rpow_neg_eq (c S : ℕ) (hS : 1 ≤ S) :
    (S : ℝ) ^ (-(1 : ℝ) / c) = 1 / (S : ℝ) ^ ((1 : ℝ) / c) := by
  rw [neg_div, Real.rpow_neg (by positivity), one_div, one_div]

/-- **`δ ≤ ε/4`** (`app:sources`, "Full-range amplification interface"). -/
theorem dyadicAcc_le (c S : ℕ) (hc : 1 ≤ c) (hS : 2 ≤ S) :
    dyadicAcc (dyadicExp c S hc) ≤ (S : ℝ) ^ (-(1 : ℝ) / c) / 4 := by
  set k := dyadicExp c S hc
  have h1 := rpow_inv_le_of_le c S k hc (le_two_pow_dyadicExp c S hc)
  have hpos : 0 < (S : ℝ) ^ ((1 : ℝ) / c) := by
    apply Real.rpow_pos_of_pos; exact_mod_cast (show 0 < S by omega)
  rw [rpow_neg_eq c S (by omega), dyadicAcc, pow_add]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **`ε/8 < δ`** (`app:sources`, "Full-range amplification interface"). -/
theorem lt_dyadicAcc (c S : ℕ) (hc : 1 ≤ c) (hS : 2 ≤ S) :
    (S : ℝ) ^ (-(1 : ℝ) / c) / 8 < dyadicAcc (dyadicExp c S hc) := by
  set k := dyadicExp c S hc
  have hk := one_le_dyadicExp c S hc hS
  have h1 := lt_rpow_inv_of_lt c S (k - 1) hc (two_pow_pred_lt c S hc hS)
  have hpos : 0 < (S : ℝ) ^ ((1 : ℝ) / c) := by
    apply Real.rpow_pos_of_pos; exact_mod_cast (show 0 < S by omega)
  have hk2 : (2 : ℝ) ^ (k + 2) = 2 ^ (k - 1) * 8 := by
    rw [show k + 2 = (k - 1) + 3 by omega, pow_add]; norm_num
  rw [rpow_neg_eq c S (by omega), dyadicAcc, hk2, div_div,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end NearCubicGates.Adapters.Amplification

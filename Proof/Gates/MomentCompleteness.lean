import Proof.Gates.CountingCore
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Literal strict even-moment completeness with the sqrt(2) slack

This closes the numerical converse in manuscript `lem:moment` without
assuming a precomputed power-sum slack inequality. The finite cardinality
is the actual cube cardinality; integer and real casts are proved explicitly.
-/

namespace NearCubicGates.CountingCore

open scoped BigOperators

theorem sqrt_two_moment_slack (k : ℕ) (hk : 1 ≤ k) (R' R : ℝ)
    (hR' : 0 ≤ R') (hmargin : Real.sqrt 2 * R' < R) :
    (2 : ℝ) ^ k * R' ^ (2 * k) < R ^ (2 * k) := by
  have hbase0 : 0 ≤ Real.sqrt 2 * R' := mul_nonneg (Real.sqrt_nonneg _) hR'
  have hsquare := pow_lt_pow_left₀ hmargin hbase0 (by decide : 2 ≠ 0)
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsquare
  have hpow := pow_lt_pow_left₀ hsquare (by positivity : (0 : ℝ) ≤ 2 * R' ^ 2)
    (by omega : k ≠ 0)
  simpa only [mul_pow, ← pow_mul] using hpow

/-- A signed integer function on a cell of at most `2^k` points passes the
literal strict moment test when its pointwise bound has the stated slack. -/
theorem finite_integer_moment_complete {Points : Type*} [Fintype Points]
    (k : ℕ) (hk : 1 ≤ k) (v : Points → ℤ) (R : ℕ) (R' : ℝ)
    (hcard : Fintype.card Points ≤ 2 ^ k) (hR' : 0 ≤ R')
    (hbound : ∀ x, (v x).natAbs ≤ R')
    (hmargin : Real.sqrt 2 * R' < (R : ℝ)) :
    (∑ x : Points, v x ^ (2 * k)) < (R : ℤ) ^ (2 * k) := by
  have hs : (∑ x : Points, ((v x).natAbs : ℝ) ^ (2 * k)) ≤
      (Fintype.card Points : ℝ) * R' ^ (2 * k) := by
    calc
      (∑ x : Points, ((v x).natAbs : ℝ) ^ (2 * k)) ≤
          ∑ _x : Points, R' ^ (2 * k) := by
        apply Finset.sum_le_sum
        intro x _
        exact pow_le_pow_left₀ (by positivity) (hbound x) (2 * k)
      _ = _ := by simp
  have hcard' : (Fintype.card Points : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcard' (pow_nonneg hR' (2 * k))
  have hslack := sqrt_two_moment_slack k hk R' R hR' hmargin
  have htotal := hs.trans_lt (hmul.trans_lt hslack)
  have hi : (∑ x : Points, v x ^ (2 * k)) =
      ∑ x : Points, (((v x).natAbs ^ (2 * k) : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro x _
    exact even_power_eq_magnitude (v x) k
  rw [hi]
  exact_mod_cast htotal

/-- The manuscript's completeness direction on the actual Boolean cube. -/
theorem boolean_cube_moment_complete (k : ℕ) (hk : 1 ≤ k)
    (v : (Fin k → Bool) → ℤ) (R : ℕ) (R' : ℝ) (hR' : 0 ≤ R')
    (hbound : ∀ x, (v x).natAbs ≤ R')
    (hmargin : Real.sqrt 2 * R' < (R : ℝ)) :
    (∑ x : Fin k → Bool, v x ^ (2 * k)) < (R : ℤ) ^ (2 * k) := by
  apply finite_integer_moment_complete k hk v R R' _ hR' hbound hmargin
  simp

end NearCubicGates.CountingCore

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# A quadratic bound for the exponential remainder

The bounded-variable Bernstein inequality in `lem:bernstein` follows by
integrating this geometric estimate for the exponential series. The estimate
keeps the linear term, so centering removes it exactly, and keeps the quadratic
term, so the resulting bound uses the variance.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Probability

/-- From degree two onward, the factorial dominates a geometric progression. -/
theorem factorial_ge_two_mul_three_pow (n : ℕ) :
    (2 : ℝ) * 3 ^ n ≤ (n + 2).factorial := by
  exact_mod_cast (show 2 * 3 ^ n ≤ (n + 2).factorial by
    simpa only [Nat.factorial, Nat.add_comm, Nat.reduceAdd, Nat.reduceMul] using
      (Nat.factorial_mul_pow_le_factorial (m := 2) (n := n)))

/-- Each term of the exponential remainder is bounded by the corresponding
geometric term. This also covers negative arguments. -/
theorem exp_tail_term_le (x b : ℝ) (hb : 0 ≤ b) (hx : |x| ≤ b) (n : ℕ) :
    x ^ (n + 2) / (n + 2).factorial ≤ (x ^ 2 / 2) * (b / 3) ^ n := by
  have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
  calc
    x ^ (n + 2) / (n + 2).factorial ≤
        |x| ^ (n + 2) / (n + 2).factorial := by
      apply div_le_div_of_nonneg_right _ hfac.le
      simpa only [abs_pow] using le_abs_self (x ^ (n + 2))
    _ = x ^ 2 * |x| ^ n / (n + 2).factorial := by
      rw [pow_add, sq_abs]
      ring
    _ ≤ x ^ 2 * b ^ n / (2 * 3 ^ n) := by
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · exact factorial_ge_two_mul_three_pow n
    _ = (x ^ 2 / 2) * (b / 3) ^ n := by
      rw [div_pow]
      ring

/-- A geometric quadratic upper bound, uniform over the interval `[-b,b]`. -/
theorem exp_le_one_add_add_quadratic (x b : ℝ) (hb : 0 ≤ b) (hb3 : b < 3)
    (hx : |x| ≤ b) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - b / 3)) := by
  have he : HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have ht : HasSum (fun n : ℕ => x ^ (n + 2) / (n + 2).factorial)
      (Real.exp x - (1 + x)) := by
    simpa [Finset.sum_range_succ, Nat.factorial] using (hasSum_nat_add_iff' 2).mpr he
  have hg := (hasSum_geometric_of_lt_one (show 0 ≤ b / 3 by positivity)
    (show b / 3 < 1 by linarith)).mul_left (x ^ 2 / 2)
  have h := hasSum_le (exp_tail_term_le x b hb hx) ht hg
  have heq : x ^ 2 / 2 * (1 - b / 3)⁻¹ = x ^ 2 / (2 * (1 - b / 3)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at h
  linarith

end NearCubicGates.Adapters.Probability

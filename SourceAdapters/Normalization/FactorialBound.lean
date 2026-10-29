import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! The determinant bound used for `lem:integer`: `(m+1)! ≤ m^m` for `m ≥ 3`. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

theorem factorial_succ_le_pow {m : ℕ} (hm : 3 ≤ m) : (m + 1).factorial ≤ m ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
      have hm1 : m - 1 + 1 = m := by omega
      have hpow : m ^ m = m * m ^ (m - 1) := by
        conv_lhs => rw [← hm1, pow_succ']
        rw [hm1]
      rw [Nat.factorial_succ]
      calc
        (m + 1 + 1) * (m + 1).factorial ≤ (m + 2) * m ^ m :=
          Nat.mul_le_mul_left (m + 2) ih
        _ = (m * (m + 2)) * m ^ (m - 1) := by rw [hpow]; ring
        _ ≤ (m + 1) ^ 2 * (m + 1) ^ (m - 1) :=
          Nat.mul_le_mul (by nlinarith) (Nat.pow_le_pow_left (by omega) _)
        _ = (m + 1) ^ (m + 1) := by
          rw [← pow_add]
          congr 1
          omega

end NearCubicGates.Adapters.Normalization

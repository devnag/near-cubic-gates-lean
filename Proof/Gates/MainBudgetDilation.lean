import Proof.Gates.Target
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! The exact integer headline budget survives constant-factor dilation.
    No real fractional powers, asymptotic floor simplifications, or resource
    renaming are needed for this step. -/

set_option autoImplicit false

namespace NearCubicGates.Target

theorem lambda_mono {q n : ℕ} (h : q ≤ n) : lambda q ≤ lambda n :=
  Nat.clog_mono_right 2 h

theorem mu_mono {q n : ℕ} (h : q ≤ n) : mu q ≤ mu n :=
  Nat.clog_mono_right 2 (lambda_mono h)

theorem mainBudget_of_weight_le {K n v w : ℕ} (hv : v ≤ w)
    (h : MainBudget K n w) : MainBudget K n v := by
  unfold MainBudget at h ⊢
  calc
    _ ≤ (K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 := by gcongr
    _ ≤ _ := h

theorem mainBudget_dilation {D B K q n w : ℕ} (hB : 0 < B)
    (hK : D * B ^ 3 ≤ K) (hq : q ≤ n) (hn : n ≤ B * q)
    (h : MainBudget K n w) : MainBudget D q w := by
  have hlambda := lambda_mono hq
  have hmu := mu_mono hq
  have hs : B ^ 12 * ((D * w * mu q ^ 7) ^ 4 * lambda q ^ 21) ≤ B ^ 12 * q ^ 12 := by
    calc
      _ = ((D * B ^ 3) * w * mu q ^ 7) ^ 4 * lambda q ^ 21 := by ring
      _ ≤ (K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 := by gcongr
      _ ≤ n ^ 12 := h
      _ ≤ (B * q) ^ 12 := Nat.pow_le_pow_left hn 12
      _ = _ := by rw [mul_pow]
  exact Nat.le_of_mul_le_mul_left hs (by positivity : 0 < B ^ 12)

end NearCubicGates.Target

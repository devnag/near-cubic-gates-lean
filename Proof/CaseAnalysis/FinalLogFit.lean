import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LogFit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The explicit onset from which `kappa * (Nat.log 2 w + 1) ≤ w`. -/
def logFit_onset (kappa : ℕ) : ℕ := 2 ^ (kappa * kappa + kappa)

/-- **`hfit`, at any width from the onset on.** -/
theorem hfit_of_onset (kappa : ℕ) :
    ∀ w, logFit_onset kappa ≤ w → kappa * (Nat.log 2 w + 1) ≤ w := by
  intro w hw
  unfold logFit_onset at hw
  have hw0 : w ≠ 0 := by
    have := Nat.two_pow_pos (kappa * kappa + kappa)
    omega
  have hL : kappa * kappa + kappa ≤ Nat.log 2 w := Nat.le_log_of_pow_le (by decide) hw
  have hpow : 2 ^ Nat.log 2 w ≤ w := Nat.pow_log_le_self 2 hw0
  obtain ⟨m, hm⟩ : ∃ m, Nat.log 2 w = m + kappa := ⟨Nat.log 2 w - kappa, by omega⟩
  have hkm : kappa * kappa ≤ m := by omega
  have h1 : kappa + 1 ≤ 2 ^ kappa := Nat.lt_two_pow_self
  have h2 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  calc kappa * (Nat.log 2 w + 1) = kappa * (m + kappa + 1) := by rw [hm]
    _ ≤ (kappa + 1) * (m + 1) := by nlinarith [hkm]
    _ ≤ 2 ^ kappa * 2 ^ m := Nat.mul_le_mul h1 h2
    _ = 2 ^ Nat.log 2 w := by rw [hm, Nat.pow_add, Nat.mul_comm]
    _ ≤ w := hpow

end NearCubicWires.RepairSource.CloseoutFinal.C10LogFit

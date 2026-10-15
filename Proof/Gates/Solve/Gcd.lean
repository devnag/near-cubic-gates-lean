import Proof.Gates.Solve.Build4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt

/-- One guarded Euclid step. -/
def eStep (p : ℕ × ℕ) : ℕ × ℕ := if p.2 = 0 then p else (p.2, p.1 % p.2)

/-- `k` steps. -/
def ePow : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | k + 1, p => ePow k (eStep p)

theorem eStep_gcd (p : ℕ × ℕ) : Nat.gcd (eStep p).1 (eStep p).2 = Nat.gcd p.1 p.2 := by
  unfold eStep
  split_ifs with h
  · rfl
  · simp only
    rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]

theorem ePow_gcd : ∀ (k : ℕ) (p : ℕ × ℕ), Nat.gcd (ePow k p).1 (ePow k p).2 = Nat.gcd p.1 p.2
  | 0, _ => rfl
  | k + 1, p => by rw [ePow, ePow_gcd k, eStep_gcd]

theorem ePow_zero_fix : ∀ (k : ℕ) (a : ℕ), ePow k (a, 0) = (a, 0)
  | 0, _ => rfl
  | k + 1, a => by rw [ePow, show eStep (a, 0) = (a, 0) by simp [eStep], ePow_zero_fix k]

theorem ePow_add : ∀ (k l : ℕ) (p : ℕ × ℕ), ePow (k + l) p = ePow l (ePow k p)
  | 0, l, p => by simp [ePow]
  | k + 1, l, p => by rw [show k + 1 + l = (k + l) + 1 by ring, ePow, ePow, ePow_add k l]

theorem two_steps (a b : ℕ) (hb : 0 < b) (hc : 0 < a % b) : 2 * (b % (a % b)) < b := by
  have h1 : a % b < b := Nat.mod_lt _ hb
  set c := a % b
  by_cases h2 : 2 * c ≤ b
  · have := Nat.mod_lt b hc; omega
  · have h3 : b % c = b - c := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem ePow_done : ∀ (j : ℕ) (a b : ℕ), b < 2 ^ j → (ePow (2 * j) (a, b)).2 = 0
  | 0, a, b, hb => by simp at hb; subst hb; simp [ePow]
  | j + 1, a, b, hb => by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; rw [ePow_zero_fix]
    · rcases Nat.eq_zero_or_pos (a % b) with hc | hc
      · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, ePow, show eStep (a, b) = (b, a % b) by simp [eStep, h0.ne'],
          hc, ePow, show eStep (b, 0) = (b, 0) by simp [eStep], ePow_zero_fix]
      · have h2 := two_steps a b h0 hc
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, ePow, show eStep (a, b) = (b, a % b) by simp [eStep, h0.ne'],
          ePow, show eStep (b, a % b) = (a % b, b % (a % b)) by simp [eStep, hc.ne']]
        exact ePow_done j _ _ (by rw [pow_succ] at hb; omega)

/-- After enough steps: `(gcd a b, 0)`. -/
theorem ePow_result (a b j : ℕ) (hb : b < 2 ^ j) : ePow (2 * j) (a, b) = (Nat.gcd a b, 0) := by
  have h1 := ePow_done j a b hb
  have h2 := ePow_gcd (2 * j) (a, b)
  rw [h1, Nat.gcd_zero_right] at h2
  ext
  · exact h2
  · exact h1

theorem ePow_le : ∀ (k : ℕ) (p : ℕ × ℕ), (ePow k p).1 ≤ max p.1 p.2 ∧ (ePow k p).2 ≤ max p.1 p.2
  | 0, p => ⟨le_max_left _ _, le_max_right _ _⟩
  | k + 1, p => by
    rw [ePow]
    have ih := ePow_le k (eStep p)
    have hs : max (eStep p).1 (eStep p).2 ≤ max p.1 p.2 := by
      unfold eStep
      split_ifs with h
      · exact le_rfl
      · have := Nat.mod_le p.1 p.2
        simp only; omega
    omega

end NearCubicGates.Close.Solve

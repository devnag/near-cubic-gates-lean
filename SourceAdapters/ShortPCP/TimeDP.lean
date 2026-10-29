import SourceAdapters.ShortPCP.TimeIter

/-!
# Single-run time, reference layer 8: the length recursion (28) as a table

BCGT13 Lemma C.10's recursion (28) for `length_{RS,=}` is transcribed with fuel (`lengthEqF`; `lengthEq T κ =
lengthEqF T κ κ`). A machine tabulates `lengthEq T0 κ'` for `κ' = 0, 1, …, f` from the smaller entries (proof of `thm:short-pcp-ours`:
the recursion halves the dimension at each level). This module gives the fuel independence (`lengthEqF_fuel`), the
recurrence on the table (`lengthEq_small`, `lengthEq_rec`), and a bound fixing the table's word width
(`lengthEq_lt`: `lengthEq T0 κ < 2^(8κ + 16)`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicGates.Published.BCGT13

theorem lengthEqF_small (n κ : ℕ) (h : κ ≤ 4) : lengthEqF T0 n κ = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [lengthEqF, T0_κ0, h]

/-- The recursion read with enough fuel. -/
theorem lengthEqF_succ (n κ : ℕ) (h : 5 ≤ κ) :
    lengthEqF T0 (n + 1) κ = 2 ^ ((κ + 1) / 2) * 2 ^ (κ / 2 + 2) + 2 ^ ((κ + 1) / 2) * lengthEqF T0 n (κ / 2 + 2) +
      2 ^ (κ / 2 + 1) * lengthEqF T0 n ((κ + 1) / 2) := by
  simp only [lengthEqF, T0_κ0, T0_γ, T0_μ, show ¬ κ ≤ 4 by omega, if_false, Nat.add_zero, Nat.sub_zero]

/-- **Fuel independence**: every fuel `n ≥ κ` gives `lengthEq T0 κ`. -/
theorem lengthEqF_fuel : ∀ (n κ : ℕ), κ ≤ n → lengthEqF T0 n κ = lengthEq T0 κ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ hκ
    by_cases h4 : κ ≤ 4
    · rw [lengthEqF_small n κ h4, lengthEq, lengthEqF_small κ κ h4]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
      rw [lengthEq, hκ', lengthEqF_succ n' _ (by omega), lengthEqF_succ κ' _ (by omega), ← hκ']
      have e1 := ih n' (by omega) (κ / 2 + 2) (by omega)
      have e2 := ih n' (by omega) ((κ + 1) / 2) (by omega)
      have e3 := ih κ' (by omega) (κ / 2 + 2) (by omega)
      have e4 := ih κ' (by omega) ((κ + 1) / 2) (by omega)
      rw [e1, e2, e3, e4]

theorem lengthEq_small (κ : ℕ) (h : κ ≤ 4) : lengthEq T0 κ = 0 := lengthEqF_small κ κ h

/-- **The table recurrence** (BCGT13 (28) with `(η, κ0, γ, μ) = (2, 4, 0, 1)`). -/
theorem lengthEq_rec (κ : ℕ) (h : 5 ≤ κ) :
    lengthEq T0 κ = 2 ^ ((κ + 1) / 2) * 2 ^ (κ / 2 + 2) + 2 ^ ((κ + 1) / 2) * lengthEq T0 (κ / 2 + 2) +
      2 ^ (κ / 2 + 1) * lengthEq T0 ((κ + 1) / 2) := by
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
  conv_lhs => rw [lengthEq, hκ', lengthEqF_succ κ' _ (by omega)]
  rw [← hκ', lengthEqF_fuel κ' _ (by omega), lengthEqF_fuel κ' _ (by omega)]

/-- **The width of the table**: `lengthEq T0 κ < 2^(8κ + 16)`. -/
theorem lengthEq_lt : ∀ κ : ℕ, lengthEq T0 κ < 2 ^ (8 * κ + 16) := by
  intro κ
  induction κ using Nat.strong_induction_on with
  | _ κ ih =>
    by_cases h4 : κ ≤ 4
    · rw [lengthEq_small κ h4]; positivity
    · rw [lengthEq_rec κ (by omega)]
      have h1 := ih (κ / 2 + 2) (by omega)
      have h2 := ih ((κ + 1) / 2) (by omega)
      have a1 : 2 ^ ((κ + 1) / 2) * 2 ^ (κ / 2 + 2) ≤ 2 ^ (8 * κ + 13) := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have a2 : 2 ^ ((κ + 1) / 2) * lengthEq T0 (κ / 2 + 2) ≤ 2 ^ (8 * κ + 14) := by
        calc 2 ^ ((κ + 1) / 2) * lengthEq T0 (κ / 2 + 2) ≤ 2 ^ ((κ + 1) / 2) * 2 ^ (8 * (κ / 2 + 2) + 16) :=
              Nat.mul_le_mul_left _ h1.le
          _ = 2 ^ ((κ + 1) / 2 + (8 * (κ / 2 + 2) + 16)) := by rw [← pow_add]
          _ ≤ 2 ^ (8 * κ + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have a3 : 2 ^ (κ / 2 + 1) * lengthEq T0 ((κ + 1) / 2) ≤ 2 ^ (8 * κ + 14) := by
        calc 2 ^ (κ / 2 + 1) * lengthEq T0 ((κ + 1) / 2) ≤ 2 ^ (κ / 2 + 1) * 2 ^ (8 * ((κ + 1) / 2) + 16) :=
              Nat.mul_le_mul_left _ h2.le
          _ = 2 ^ (κ / 2 + 1 + (8 * ((κ + 1) / 2) + 16)) := by rw [← pow_add]
          _ ≤ 2 ^ (8 * κ + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : 2 ^ (8 * κ + 16) = 2 ^ (8 * κ + 13) * 8 := by rw [show 8 * κ + 16 = 8 * κ + 13 + 3 by ring, pow_add]; norm_num
      have e2 : 2 ^ (8 * κ + 14) = 2 ^ (8 * κ + 13) * 2 := by rw [pow_succ]
      have := Nat.one_le_two_pow (n := 8 * κ + 13)
      omega

end NearCubicGates.Adapters.ShortPCP.Time

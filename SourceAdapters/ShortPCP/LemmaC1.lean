import NineInputs
import Mathlib.Tactic.IntervalCases

/-!
# Fixed-tuple Reed–Solomon recursion bounds

`lem:rs-recursion` proves the randomness and length estimates at
`(η,κ0,γ,μ) = (2,4,0,1)` directly from the recursions (27) and (28)
of BCGT13 Lemmas C.9 and C.10, transcribed as `randEq` and `lengthEq`.
These are the bounds used in Step 2(a) of `thm:short-pcp-ours`.

The theorem `lemmaC1` proves, for every κ ≥ 1,
`randEq κ ≤ κ + 3·log₂(2κ)` and `lengthEq κ ≤ 2^κ·κ^3`.
The induction gives, for κ ≥ 5 and κ−4 < 2^j,
`randEq κ + 3 ≤ κ + 3j` and `lengthEq κ + 2^κ ≤ 2^κ·6^j`;
then `6^(m+1) ≤ (2^m+4)^3` with `m = ⌊log₂(κ−4)⌋` closes the bound.
The general published Lemma C.1 is not assumed; see `rem:bcgt-c1`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Published.BCGT13

namespace LemmaC1

/-- The tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`. -/
local notation "T₀" => (⟨2, 4, 0, 1⟩ : Tuple)

/-! ## The recursions at `T₀` -/

theorem randEqF_small (n κ : ℕ) (h : κ ≤ 4) : randEqF T₀ n κ = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [randEqF, h]

theorem randEqF_step (n κ : ℕ) (h : 5 ≤ κ) :
    randEqF T₀ (n + 1) κ =
      1 + max ((κ + 1) / 2 + randEqF T₀ n (κ / 2 + 2)) (κ / 2 + 1 + randEqF T₀ n ((κ + 1) / 2)) := by
  rw [randEqF, if_neg (show ¬ κ ≤ 4 by omega)]
  rfl

theorem randEqF_eq : ∀ (n κ : ℕ), κ ≤ n → randEqF T₀ n κ = randEq T₀ κ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ hκ
    by_cases h4 : κ ≤ 4
    · rw [randEqF_small n κ h4, randEq, randEqF_small κ κ h4]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
      rw [randEq, hκ', randEqF_step n' _ (by omega), randEqF_step κ' _ (by omega), ← hκ']
      rw [ih n' (by omega) (κ / 2 + 2) (by omega), ih n' (by omega) ((κ + 1) / 2) (by omega),
        ih κ' (by omega) (κ / 2 + 2) (by omega), ih κ' (by omega) ((κ + 1) / 2) (by omega)]

theorem randEq_small (κ : ℕ) (h : κ ≤ 4) : randEq T₀ κ = 0 := randEqF_small κ κ h

/-- Recursion (27) at `T₀`: `r(κ) = 1 + max{⌈κ/2⌉ + r(⌊κ/2⌋ + 2), ⌊κ/2⌋ + 1 + r(⌈κ/2⌉)}` for `κ > 4`. -/
theorem randEq_step (κ : ℕ) (h : 5 ≤ κ) :
    randEq T₀ κ = 1 + max ((κ + 1) / 2 + randEq T₀ (κ / 2 + 2)) (κ / 2 + 1 + randEq T₀ ((κ + 1) / 2)) := by
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
  conv_lhs => rw [randEq, hκ', randEqF_step κ' _ (by omega)]
  rw [← hκ', randEqF_eq κ' _ (by omega), randEqF_eq κ' _ (by omega)]

theorem lengthEqF_small (n κ : ℕ) (h : κ ≤ 4) : lengthEqF T₀ n κ = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [lengthEqF, h]

theorem lengthEqF_step (n κ : ℕ) (h : 5 ≤ κ) :
    lengthEqF T₀ (n + 1) κ = 2 ^ ((κ + 1) / 2) * 2 ^ (κ / 2 + 2) +
      2 ^ ((κ + 1) / 2) * lengthEqF T₀ n (κ / 2 + 2) + 2 ^ (κ / 2 + 1) * lengthEqF T₀ n ((κ + 1) / 2) := by
  rw [lengthEqF, if_neg (show ¬ κ ≤ 4 by omega)]
  rfl

theorem lengthEqF_eq : ∀ (n κ : ℕ), κ ≤ n → lengthEqF T₀ n κ = lengthEq T₀ κ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ hκ
    by_cases h4 : κ ≤ 4
    · rw [lengthEqF_small n κ h4, lengthEq, lengthEqF_small κ κ h4]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
      rw [lengthEq, hκ', lengthEqF_step n' _ (by omega), lengthEqF_step κ' _ (by omega), ← hκ']
      rw [ih n' (by omega) (κ / 2 + 2) (by omega), ih n' (by omega) ((κ + 1) / 2) (by omega),
        ih κ' (by omega) (κ / 2 + 2) (by omega), ih κ' (by omega) ((κ + 1) / 2) (by omega)]

theorem lengthEq_small (κ : ℕ) (h : κ ≤ 4) : lengthEq T₀ κ = 0 := lengthEqF_small κ κ h

/-- Recursion (28) at `T₀`: `L(κ) = 2^{⌈κ/2⌉}·2^{⌊κ/2⌋+2} + 2^{⌈κ/2⌉} L(⌊κ/2⌋ + 2) + 2^{⌊κ/2⌋+1} L(⌈κ/2⌉)` for
`κ > 4`. -/
theorem lengthEq_step (κ : ℕ) (h : 5 ≤ κ) :
    lengthEq T₀ κ = 2 ^ ((κ + 1) / 2) * 2 ^ (κ / 2 + 2) +
      2 ^ ((κ + 1) / 2) * lengthEq T₀ (κ / 2 + 2) + 2 ^ (κ / 2 + 1) * lengthEq T₀ ((κ + 1) / 2) := by
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
  conv_lhs => rw [lengthEq, hκ', lengthEqF_step κ' _ (by omega)]
  rw [← hκ', lengthEqF_eq κ' _ (by omega), lengthEqF_eq κ' _ (by omega)]

/-! ## The two bounds -/

/-- **Randomness, inductive form**: for `κ ≥ 5` and `κ − 4 < 2^j`, `rand_{RS,=}(κ) + 3 ≤ κ + 3j`. -/
theorem randEq_add_le : ∀ κ : ℕ, 5 ≤ κ → ∀ j : ℕ, κ - 4 < 2 ^ j → randEq T₀ κ + 3 ≤ κ + 3 * j := by
  intro κ
  induction κ using Nat.strong_induction_on with
  | _ κ ih =>
    intro hκ j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
      rcases j with _ | j
      · simp at hj; omega
      · exact ⟨j, rfl⟩
    rw [pow_succ] at hj
    have ha : randEq T₀ (κ / 2 + 2) + 3 ≤ κ / 2 + 2 + 3 * j ∨ randEq T₀ (κ / 2 + 2) = 0 := by
      by_cases h5 : 5 ≤ κ / 2 + 2
      · exact Or.inl (ih _ (by omega) h5 j (by omega))
      · exact Or.inr (randEq_small _ (by omega))
    have hb : randEq T₀ ((κ + 1) / 2) + 3 ≤ (κ + 1) / 2 + 3 * j ∨ randEq T₀ ((κ + 1) / 2) = 0 := by
      by_cases h5 : 5 ≤ (κ + 1) / 2
      · exact Or.inl (ih _ (by omega) h5 j (by omega))
      · exact Or.inr (randEq_small _ (by omega))
    rw [randEq_step κ hκ]
    omega

/-- **Randomness** (Lemma C.1 at `T₀`): `rand_{RS,=}(κ) ≤ κ + 3·log₂(2κ)` for `κ ≥ 1`. -/
theorem randEq_le_real (κ : ℕ) (hκ : 1 ≤ κ) : (randEq T₀ κ : ℝ) ≤ κ + 3 * Real.logb 2 (2 * κ) := by
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hlog0 : 0 ≤ Real.logb 2 (2 * κ) := Real.logb_nonneg (by norm_num) (by linarith)
  by_cases h4 : κ ≤ 4
  · rw [randEq_small κ h4]
    push_cast
    nlinarith
  · set m := Nat.log 2 (κ - 4) with hm
    have hlt : κ - 4 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hle : 2 ^ m ≤ κ - 4 := Nat.pow_log_le_self 2 (by omega)
    have hN := randEq_add_le κ (by omega) (m + 1) hlt
    have h2 : 2 ^ (m + 1) ≤ 2 * κ := by rw [pow_succ]; omega
    have hjr : ((m + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2 * κ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
      exact_mod_cast h2
    have hNr : (randEq T₀ κ : ℝ) + 3 ≤ κ + 3 * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hN
    linarith

/-- **Length, inductive form**: for `κ ≥ 5` and `κ − 4 < 2^j`, `length_{RS,=}(κ) + 2^κ ≤ 2^κ·6^j`. -/
theorem lengthEq_add_le :
    ∀ κ : ℕ, 5 ≤ κ → ∀ j : ℕ, κ - 4 < 2 ^ j → lengthEq T₀ κ + 2 ^ κ ≤ 2 ^ κ * 6 ^ j := by
  intro κ
  induction κ using Nat.strong_induction_on with
  | _ κ ih =>
    intro hκ j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
      rcases j with _ | j
      · simp at hj; omega
      · exact ⟨j, rfl⟩
    rw [pow_succ] at hj
    have hQ : 1 ≤ 6 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have eab : 2 ^ ((κ + 1) / 2) * 2 ^ (κ / 2 + 2) = 4 * 2 ^ κ := by
      rw [← pow_add, show (κ + 1) / 2 + (κ / 2 + 2) = κ + 2 by omega, pow_add]; ring
    have eba : 2 ^ (κ / 2 + 1) * 2 ^ ((κ + 1) / 2) = 2 * 2 ^ κ := by
      rw [← pow_add, show κ / 2 + 1 + (κ + 1) / 2 = κ + 1 by omega, pow_succ]; ring
    -- the child `⌊κ/2⌋ + 2`
    have hX : 2 ^ ((κ + 1) / 2) * lengthEq T₀ (κ / 2 + 2) + 4 * 2 ^ κ ≤ 4 * 2 ^ κ * 6 ^ j := by
      by_cases h5 : 5 ≤ κ / 2 + 2
      · have h := ih _ (by omega) h5 j (by omega)
        have h' := Nat.mul_le_mul_left (2 ^ ((κ + 1) / 2)) h
        rw [mul_add, ← mul_assoc, eab] at h'
        exact h'
      · rw [lengthEq_small _ (by omega), mul_zero, zero_add]
        exact Nat.le_mul_of_pos_right _ hQ
    -- the child `⌈κ/2⌉`
    have hY : 2 ^ (κ / 2 + 1) * lengthEq T₀ ((κ + 1) / 2) + 2 * 2 ^ κ ≤ 2 * 2 ^ κ * 6 ^ j := by
      by_cases h5 : 5 ≤ (κ + 1) / 2
      · have h := ih _ (by omega) h5 j (by omega)
        have h' := Nat.mul_le_mul_left (2 ^ (κ / 2 + 1)) h
        rw [mul_add, ← mul_assoc, eba] at h'
        exact h'
      · rw [lengthEq_small _ (by omega), mul_zero, zero_add]
        exact Nat.le_mul_of_pos_right _ hQ
    rw [lengthEq_step κ hκ, eab,
      show 2 ^ κ * 6 ^ (j + 1) = 4 * 2 ^ κ * 6 ^ j + 2 * 2 ^ κ * 6 ^ j by ring]
    omega

/-- `6^{m+1} ≤ (2^m + 4)^3` (equality at `m = 5`). -/
theorem six_pow_le (m : ℕ) : 6 ^ (m + 1) ≤ (2 ^ m + 4) ^ 3 := by
  by_cases hm : m < 7
  · interval_cases m <;> norm_num
  · have h8 : ∀ k : ℕ, 7 ≤ k → 6 ^ (k + 1) ≤ 8 ^ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k _ ih =>
        rw [pow_succ 6, pow_succ 8]
        omega
    calc 6 ^ (m + 1) ≤ 8 ^ m := h8 m (by omega)
      _ = (2 ^ m) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (2 ^ m + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3

/-- **Length** (Lemma C.1 at `T₀`): `length_{RS,=}(κ) ≤ 2^κ κ^3`. -/
theorem lengthEq_le (κ : ℕ) : lengthEq T₀ κ ≤ 2 ^ κ * κ ^ 3 := by
  by_cases h4 : κ ≤ 4
  · rw [lengthEq_small κ h4]; exact Nat.zero_le _
  · set m := Nat.log 2 (κ - 4) with hm
    have hlt : κ - 4 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hle : 2 ^ m ≤ κ - 4 := Nat.pow_log_le_self 2 (by omega)
    have hN := lengthEq_add_le κ (by omega) (m + 1) hlt
    have h6 : 6 ^ (m + 1) ≤ κ ^ 3 :=
      (six_pow_le m).trans (Nat.pow_le_pow_left (by omega) 3)
    calc lengthEq T₀ κ ≤ 2 ^ κ * 6 ^ (m + 1) := le_trans (Nat.le_add_right _ _) hN
      _ ≤ 2 ^ κ * κ ^ 3 := Nat.mul_le_mul_left _ h6

end LemmaC1

/-- **BCGT13 Lemma C.1 at the tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`** of the single-run verifier: for every `κ ≥ 1`,
`rand_{RS,=}(κ) ≤ κ + (μ+2)·log₂(2κ) = κ + 3·log₂(2κ)` and
`length_{RS,=}(κ) ≤ 2^κ κ^{1+max{μ+1−γ,γ}} = 2^κ κ^3`. -/
theorem lemmaC1 (κ : ℕ) (hκ : 1 ≤ κ) :
    (randEq ⟨2, 4, 0, 1⟩ κ : ℝ) ≤ κ + 3 * Real.logb 2 (2 * κ) ∧ lengthEq ⟨2, 4, 0, 1⟩ κ ≤ 2 ^ κ * κ ^ 3 :=
  ⟨LemmaC1.randEq_le_real κ hκ, LemmaC1.lengthEq_le κ⟩

end NearCubicGates.Adapters.ShortPCP

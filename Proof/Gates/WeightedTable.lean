import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Minimum-error cofactors and the five-position table

This file formalizes the finite weighted selection inequality in
`eq:gadget-table-error`.  It does not construct the PCP table or a machine.
The incidence lower bound is an explicit combinatorial premise, not a
published assumption or an asserted theorem about the whole construction.
-/

namespace NearCubicGates.WeightedTable
open scoped BigOperators

variable {Name Address : Type*}

/-- A minimizing cofactor exists on every nonempty finite occurrence set. -/
theorem minimizing_address (s : Finset Address) (err : Address → ℝ)
    (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, err a ≤ err b := s.exists_min_image err hne

/-- One group's minimum is no greater than its average, in a form that
avoids division and is also correct for empty groups. -/
theorem group_minimum_bound (s : Finset Address) (err : Address → ℝ)
    (e : ℝ) (hmin : ∀ a ∈ s, e ≤ err a) :
    (s.card : ℝ) * e ≤ ∑ a ∈ s, err a := by
  calc
    _ = ∑ _a ∈ s, e := by simp
    _ ≤ _ := Finset.sum_le_sum hmin

/-- If a name of stability weight `w` has at least `t*w` table positions,
the cost of its best cofactor is paid by the errors on those positions. -/
theorem weighted_group_bound (s : Finset Address) (err : Address → ℝ)
    (t w e : ℝ) (he : 0 ≤ e)
    (hcount : t * w ≤ (s.card : ℝ))
    (hmin : ∀ a ∈ s, e ≤ err a) :
    t * (w * e) ≤ ∑ a ∈ s, err a := by
  calc
    _ = (t * w) * e := by ring
    _ ≤ (s.card : ℝ) * e := mul_le_mul_of_nonneg_right hcount he
    _ ≤ _ := group_minimum_bound s err e hmin

theorem weighted_table_bound (names : Finset Name)
    (positions : Name → Finset Address) (err : Address → ℝ)
    (weight chosenError : Name → ℝ) (t : ℝ)
    (he : ∀ x ∈ names, 0 ≤ chosenError x)
    (hc : ∀ x ∈ names, t * weight x ≤ ((positions x).card : ℝ))
    (hm : ∀ x ∈ names, ∀ a ∈ positions x, chosenError x ≤ err a) :
    t * (∑ x ∈ names, weight x * chosenError x) ≤
      ∑ x ∈ names, ∑ a ∈ positions x, err a := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact weighted_group_bound (positions x) err t (weight x) (chosenError x)
    (he x hx) (hc x hx) (hm x hx)

/-- Division by table and gadget sizes yields the exact factor of `eq:gadget-table-error`. -/
theorem normalized_table_bound (penalty errorTotal R P t δ : ℝ)
    (hR : 0 < R) (ht : 0 < t)
    (hpenalty : R * t * penalty ≤ errorTotal)
    (herror : errorTotal = R * P * δ) :
    penalty ≤ (P / t) * δ := by
  have hcancel : t * penalty ≤ P * δ := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hpenalty]
  calc
    penalty ≤ P * δ / t := by
      apply (le_div_iff₀ ht).mpr
      nlinarith
    _ = (P / t) * δ := by ring

/-- Finite arithmetic reserve: P/floor(P/5) approaches five.
The hypotheses are exactly the inequalities supplied by the floor rule.
For `P_q = 128/ε_q` (`eq:gadget-parameters`), the numerical premise has generous slack. -/
theorem five_position_factor (P t ε : ℝ)
    (ht : 0 < t) (hε : 0 < ε) (hε₁ : ε < 1)
    (hfloor : P - 5 < 5 * t) (hlarge : 128 ≤ ε * P) :
    P / t ≤ 5 + ε := by
  apply (div_le_iff₀ ht).mpr
  have hmult := mul_lt_mul_of_pos_left hfloor hε
  nlinarith

end NearCubicGates.WeightedTable

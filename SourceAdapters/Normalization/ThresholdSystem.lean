import SourceAdapters.Normalization.IntegerSeparator
import SourceAdapters.Normalization.FiniteMargin
import Mathlib.Data.Fintype.BigOperators

/-!
# The finite inequality system of a Boolean threshold

For `lem:integer`, an input contributes its affine row `(x,-1)`, signed by
the threshold's answer. A finite margin shift respects the inclusive tie rule.
The affine Boolean rows span the whole coefficient space, as witnessed by
the zero input and the singleton inputs.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

open Matrix

variable {κ : Type*} [Fintype κ]

def affineRow (x : κ → Bool) : Option κ → ℤ
  | none => -1
  | some j => if x j then 1 else 0

def thresholdScore (w : κ → ℝ) (t : ℝ) (x : κ → Bool) : ℝ :=
  (∑ j, w j * (if x j then 1 else 0)) - t

noncomputable def thresholdRows (w : κ → ℝ) (t : ℝ) : Matrix (κ → Bool) (Option κ) ℤ :=
  fun x j => if 0 ≤ thresholdScore w t x then affineRow x j else -affineRow x j

theorem affineRow_real_dot (x : κ → Bool) (v : Option κ → ℝ) :
    (fun j => (affineRow x j : ℝ)) ⬝ᵥ v =
      (∑ j, v (some j) * (if x j then 1 else 0)) - v none := by
  simp [dotProduct, Fintype.sum_option, affineRow, sub_eq_add_neg, mul_comm, add_comm]

theorem affineRow_int_dot (x : κ → Bool) (v : Option κ → ℤ) :
    affineRow x ⬝ᵥ v = (∑ j, v (some j) * (if x j then 1 else 0)) - v none := by
  simp [dotProduct, Fintype.sum_option, affineRow, sub_eq_add_neg, mul_comm, add_comm]

theorem affineRow_separates (v : Option κ → ℝ)
    (hv : ∀ x : κ → Bool, (fun j => (affineRow x j : ℝ)) ⬝ᵥ v = 0) : v = 0 := by
  classical
  have h0 : v none = 0 := by
    have h := hv (fun _ => false)
    simpa only [affineRow_real_dot, Bool.false_eq_true, if_false, mul_zero,
      Finset.sum_const_zero, zero_sub, neg_eq_zero] using h
  have h1 (j : κ) : v (some j) = 0 := by
    have h := hv (fun i => decide (i = j))
    simpa [affineRow_real_dot, h0] using h
  funext j
  cases j with
  | none => exact h0
  | some j => exact h1 j

theorem thresholdRows_abs_le (w : κ → ℝ) (t : ℝ) (x : κ → Bool) (j : Option κ) :
    |thresholdRows w t x j| ≤ 1 := by
  have h : |affineRow x j| ≤ 1 := by
    cases j with
    | none => norm_num [affineRow]
    | some j => cases hx : x j <;> norm_num [affineRow, hx]
  unfold thresholdRows
  split <;> simpa only [abs_neg] using h

theorem thresholdRows_separates (w : κ → ℝ) (t : ℝ) (v : Option κ → ℝ)
    (hv : ∀ x : κ → Bool, (fun j => (thresholdRows w t x j : ℝ)) ⬝ᵥ v = 0) : v = 0 := by
  apply affineRow_separates v
  intro x
  have h := hv x
  by_cases hx : 0 ≤ thresholdScore w t x
  · simpa only [thresholdRows, if_pos hx] using h
  · simpa only [thresholdRows, if_neg hx, Int.cast_neg, dotProduct, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] using h

theorem thresholdRows_feasible (w : κ → ℝ) (t : ℝ) :
    ∃ v : Option κ → ℝ, ∀ x : κ → Bool,
      1 ≤ (fun j => (thresholdRows w t x j : ℝ)) ⬝ᵥ v := by
  classical
  obtain ⟨δ, c, _, _, hmargin⟩ := exists_signed_unit_margin (thresholdScore w t)
  let v : Option κ → ℝ := fun j => c * j.elim (t - δ) w
  refine ⟨v, ?_⟩
  intro x
  have hv : (fun j => (affineRow x j : ℝ)) ⬝ᵥ v = c * (thresholdScore w t x + δ) := by
    rw [affineRow_real_dot]
    simp only [v, Option.elim_some, Option.elim_none, thresholdScore]
    rw [show (∑ j, c * w j * (if x j then 1 else 0)) =
      c * ∑ j, w j * (if x j then 1 else 0) by simp only [Finset.mul_sum, mul_assoc]]
    ring
  by_cases hx : 0 ≤ thresholdScore w t x
  · simpa only [thresholdRows, if_pos hx, hv, one_mul] using hmargin x
  · simp only [thresholdRows, if_neg hx, Int.cast_neg]
    change 1 ≤ (-(fun j => (affineRow x j : ℝ))) ⬝ᵥ v
    rw [neg_dotProduct, hv]
    simpa only [if_neg hx, neg_one_mul] using hmargin x

/-- Integer parameters for a threshold over any finite Boolean coordinate set.
The bound is the factorial of the affine coefficient dimension. -/
theorem exists_integer_threshold (w : κ → ℝ) (t : ℝ) :
    ∃ (a : κ → ℤ) (b : ℤ),
      (∀ x : κ → Bool,
        (t ≤ ∑ j, w j * (if x j then 1 else 0)) ↔
          (b ≤ ∑ j, a j * (if x j then 1 else 0))) ∧
      (∀ j, |a j| ≤ (Nat.factorial (Fintype.card κ + 1) : ℤ)) ∧
      |b| ≤ (Nat.factorial (Fintype.card κ + 1) : ℤ) := by
  classical
  obtain ⟨z, hz, hbound⟩ := exists_integer_separator (thresholdRows w t)
    (thresholdRows_abs_le w t) (thresholdRows_separates w t) (thresholdRows_feasible w t)
  refine ⟨fun j => z (some j), z none, ?_, ?_, ?_⟩
  · intro x
    have h := hz x
    change 0 < (fun j => thresholdRows w t x j) ⬝ᵥ z at h
    by_cases hx : 0 ≤ thresholdScore w t x
    · have hs : z none < ∑ j, z (some j) * (if x j then 1 else 0) := by
        simpa only [thresholdRows, if_pos hx, affineRow_int_dot, sub_pos] using h
      exact iff_of_true (sub_nonneg.mp hx) hs.le
    · have hs : (∑ j, z (some j) * (if x j then 1 else 0)) < z none := by
        have hh : 0 < -(affineRow x ⬝ᵥ z) := by
          simp only [thresholdRows, if_neg hx] at h
          change 0 < (-affineRow x) ⬝ᵥ z at h
          simpa only [neg_dotProduct] using h
        rw [affineRow_int_dot] at hh
        linarith
      exact iff_of_false (by simpa only [thresholdScore, sub_nonneg] using hx) (not_le.mpr hs)
  · intro j
    simpa only [Fintype.card_option] using hbound (some j)
  · simpa only [Fintype.card_option] using hbound none

end NearCubicGates.Adapters.Normalization

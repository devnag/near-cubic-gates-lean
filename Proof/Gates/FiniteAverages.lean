import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import StatementSupport

set_option autoImplicit false

namespace NearCubicGates.FiniteAverages

open scoped BigOperators

theorem mean_le_mean {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x)
  positivity

@[simp] theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  simp [mean, Fintype.card_ne_zero]

theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

theorem mean_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

theorem card_mul_mean {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (Fintype.card α : ℝ) * mean f = ∑ x, f x := by
  unfold mean
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem mean_finset_sum {α ι : Type*} [Fintype α] (s : Finset ι)
    (f : ι → α → ℝ) : mean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    mean f = mean (fun y => mean (fun x => f (x, y))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div, div_div]

theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (E : α ≃ β) (f : β → ℝ) : mean (fun a => f (E a)) = mean f := by
  unfold mean
  rw [E.sum_comp, Fintype.card_congr E]

theorem mean_mean_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    mean (fun a => mean (f a)) = mean (fun b => mean (fun a => f a b)) := by
  simp only [mean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm]

theorem exists_le_mean {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, f x ≤ mean f := by
  obtain ⟨x, _, hx⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
  refine ⟨x, ?_⟩
  have hs : (Fintype.card α : ℝ) * f x ≤ ∑ y, f y := by
    calc
      _ = ∑ _y : α, f x := by simp
      _ ≤ _ := Finset.sum_le_sum fun y hy => hx y hy
  exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos)).mpr (by nlinarith)

theorem exists_mean_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, mean f ≤ f x := by
  obtain ⟨x, hx⟩ := exists_le_mean (fun y => -f y)
  refine ⟨x, ?_⟩
  simp only [mean, Finset.sum_neg_distrib, neg_div] at hx ⊢
  linarith

noncomputable def mismatch (a b : Bool) : ℝ := if a = b then 0 else 1

theorem mismatch_nonneg (a b : Bool) : 0 ≤ mismatch a b := by
  unfold mismatch; split <;> norm_num

theorem mismatch_not (a b : Bool) : mismatch (!a) (!b) = mismatch a b := by
  cases a <;> cases b <;> rfl

noncomputable def error {α : Type*} [Fintype α] (f g : α → Bool) : ℝ :=
  mean (fun x => mismatch (f x) (g x))

noncomputable def agreement {α : Type*} [Fintype α] (f g : α → Bool) : ℝ :=
  mean (fun x => if f x = g x then 1 else 0)

theorem error_add_agreement {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → Bool) : error f g + agreement f g = 1 := by
  rw [error, agreement, ← mean_add]
  have hp : (fun x => mismatch (f x) (g x) + if f x = g x then 1 else 0) =
      (fun _ : α => (1 : ℝ)) := by
    funext x
    by_cases h : f x = g x <;> simp [mismatch, h]
  rw [hp, mean_const]

theorem error_nonneg {α : Type*} [Fintype α] [Nonempty α] (f g : α → Bool) :
    0 ≤ error f g := by
  have := mean_le_mean (fun _ : α => 0) (fun x => mismatch (f x) (g x))
    (fun x => mismatch_nonneg (f x) (g x))
  simpa [error] using this

theorem error_not {α : Type*} [Fintype α] (f g : α → Bool) :
    error (fun x => !(f x)) (fun x => !(g x)) = error f g := by
  simp [error, mismatch_not]

@[simp] theorem error_self {α : Type*} [Fintype α] (f : α → Bool) : error f f = 0 := by
  simp [error, mean, mismatch]

end NearCubicGates.FiniteAverages

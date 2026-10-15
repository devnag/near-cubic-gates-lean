import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Rat

/-!
# Finite signed distributions and exact push-forwards

These operations are on actual rational masses, not point-value CRT data.
They will be used to commute two-score modular measurements with projections.
-/

namespace NearCubicGates.FiniteDistributions

open scoped BigOperators

variable {A B C : Type*} [Fintype A]

/-- Total signed mass in a fiber of a finite map. -/
def pushforward [DecidableEq B] (f : A → B) (mass : A → ℚ) (b : B) : ℚ :=
  ∑ a : A, if f a = b then mass a else 0

theorem pushforward_zero [DecidableEq B] (f : A → B) :
    pushforward f (fun _ => 0) = fun _ => 0 := by
  funext b
  simp [pushforward]

theorem pushforward_sub [DecidableEq B] (f : A → B) (mass₁ mass₂ : A → ℚ) :
    pushforward f (fun a => mass₁ a - mass₂ a) =
      fun b => pushforward f mass₁ b - pushforward f mass₂ b := by
  funext b
  simp only [pushforward, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem pushforward_congr [DecidableEq B] {f g : A → B}
    (hfg : ∀ a, f a = g a) (mass : A → ℚ) :
    pushforward f mass = pushforward g mass := by
  have h : f = g := funext hfg
  rw [h]

/-- Exact commutation of a projection with a push-forward, including signed masses. -/
theorem pushforward_comp [Fintype B] [DecidableEq B] [DecidableEq C]
    (f : A → B) (g : B → C) (mass : A → ℚ) :
    pushforward g (pushforward f mass) = pushforward (g ∘ f) mass := by
  funext c
  simp only [pushforward, Function.comp_apply]
  have hsplit (b : B) :
      (if g b = c then ∑ a : A, if f a = b then mass a else 0 else 0) =
        ∑ a : A, if g b = c then (if f a = b then mass a else 0) else 0 := by
    by_cases h : g b = c <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

theorem pushforward_id [DecidableEq A] (mass : A → ℚ) :
    pushforward id mass = mass := by
  funext a
  change (∑ x : A, if x = a then mass x else 0) = mass a
  rw [Finset.sum_ite_eq']
  simp

/-- Push-forward preserves the full signed total, without a positivity premise. -/
theorem pushforward_total [Fintype B] [DecidableEq B]
    (f : A → B) (mass : A → ℚ) :
    (∑ b : B, pushforward f mass b) = ∑ a : A, mass a := by
  simp only [pushforward]
  rw [Finset.sum_comm]
  simp

end NearCubicGates.FiniteDistributions

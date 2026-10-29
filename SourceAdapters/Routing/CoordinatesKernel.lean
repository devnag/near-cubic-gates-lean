import SourceAdapters.Routing.CoordinatesStep

/-! # Recursive annihilator and its exact Boolean-span kernel

The recursion is valid for arbitrary basis candidates, including dependent ones.
The nonzero-pivot theorem explicitly requires the next vector to lie outside
the prior Boolean span. No independence or successful pivot is hidden in a definition.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial

variable {F : Type*} [Field F]

/-- Boolean combinations of the first `n` basis candidates, recursively.
In characteristic two, the second branch is translation by the next vector. -/
def prefixSpan (e : ℕ → F) : ℕ → Set F
  | 0 => {0}
  | n + 1 => prefixSpan e n ∪ {x | x + e n ∈ prefixSpan e n}

/-- The actual sequence of annihilator polynomials computed by the solver. -/
def annihilator (e : ℕ → F) : ℕ → F[X]
  | 0 => X
  | n + 1 => annihilatorStep (annihilator e n) (e n)

theorem zero_mem_prefixSpan (e : ℕ → F) (n : ℕ) : (0 : F) ∈ prefixSpan e n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Or.inl ih

theorem prefixSpan_mono (e : ℕ → F) {n m : ℕ} (hnm : n ≤ m) :
    prefixSpan e n ⊆ prefixSpan e m := by
  induction m, hnm using Nat.le_induction with
  | base => exact Set.Subset.refl _
  | succ m _ ih => exact fun _ hx => Or.inl (ih hx)

theorem basis_mem_prefixSpan [CharP F 2] (e : ℕ → F) {i n : ℕ} (hi : i < n) :
    e i ∈ prefixSpan e n := by
  apply prefixSpan_mono e hi
  change e i ∈ prefixSpan e i ∨ e i + e i ∈ prefixSpan e i
  exact Or.inr (by simpa only [CharTwo.add_self_eq_zero] using zero_mem_prefixSpan e i)

theorem annihilator_additive [CharP F 2] (e : ℕ → F) (n : ℕ) (x y : F) :
    (annihilator e n).eval (x + y) =
      (annihilator e n).eval x + (annihilator e n).eval y := by
  induction n generalizing x y with
  | zero => simp [annihilator]
  | succ n ih =>
    exact annihilatorStep_additive (annihilator e n) (e n) ih x y

/-- Every stage has exactly the intended kernel, without a root-enumeration argument. -/
theorem annihilator_kernel [CharP F 2] (e : ℕ → F) (n : ℕ) (x : F) :
    (annihilator e n).eval x = 0 ↔ x ∈ prefixSpan e n := by
  induction n generalizing x with
  | zero => simp [annihilator, prefixSpan]
  | succ n ih =>
    rw [annihilator, annihilatorStep_kernel_translate _ _ (annihilator_additive e n)]
    change (_ ∨ _) ↔ (x ∈ prefixSpan e n ∨ x + e n ∈ prefixSpan e n)
    exact or_congr (ih x) (ih (x + e n))

/-- Inversion is permitted exactly when the next basis candidate is independent
of its predecessors in the stated Boolean-span sense. -/
theorem pivot_ne_zero_iff [CharP F 2] (e : ℕ → F) (n : ℕ) :
    (annihilator e n).eval (e n) ≠ 0 ↔ e n ∉ prefixSpan e n := by
  exact not_congr (annihilator_kernel e n (e n))

theorem annihilator_at_basis [CharP F 2] (e : ℕ → F) {i n : ℕ} (hi : i < n) :
    (annihilator e n).eval (e i) = 0 := by
  exact (annihilator_kernel e n (e i)).mpr (basis_mem_prefixSpan e hi)

end NearCubicGates.Adapters.Routing.Coordinates

import SourceAdapters.Routing.CoordinatesKernel
import SourceAdapters.Routing.CoordinatesDegree
import Lean.Elab.Tactic.Omega

/-! # Actual recursive coordinate polynomials and their basis values

The matrix is represented by a total row function; only rows below the stage
are used. The pivot premise is discharged by `pivot_ne_zero_iff` from the
independence of the input basis. This file makes no machine-cost claim.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial

variable {F : Type*} [Field F]

def coordinates (e : ℕ → F) : ℕ → ℕ → F[X]
  | 0, _ => 0
  | n + 1, j =>
      if j = n then unitStep (annihilator e n) (e n)
      else coordinateStep (annihilator e n) (coordinates e n j) (e n)

theorem coordinates_on_basis [CharP F 2] (e : ℕ → F) (n : ℕ)
    (hp : ∀ k < n, (annihilator e k).eval (e k) ≠ 0)
    (j i : ℕ) (hj : j < n) (hi : i < n) :
    (coordinates e n j).eval (e i) = if j = i then 1 else 0 := by
  induction n generalizing j i with
  | zero => omega
  | succ n ih =>
    have hn := hp n (Nat.lt_succ_self n)
    by_cases hjn : j = n
    · subst j
      rw [coordinates, if_pos rfl]
      by_cases hin : i = n
      · subst i
        simpa using unitStep_eval_self (annihilator e n) (e n) hn
      · have hi' : i < n := by omega
        simpa [Ne.symm hin] using
          unitStep_eval_at_root (annihilator e n) (e n) (e i) (annihilator_at_basis e hi')
    · rw [coordinates, if_neg hjn]
      by_cases hin : i = n
      · subst i
        simpa [hjn] using
          coordinateStep_eval_self (annihilator e n) (coordinates e n j) (e n) hn
      · have hi' : i < n := by omega
        have hj' : j < n := by omega
        rw [coordinateStep_eval_at_root _ _ _ _ (annihilator_at_basis e hi')]
        exact ih (fun k hk => hp k (Nat.lt_trans hk (Nat.lt_succ_self n))) j i hj' hi'

theorem coordinates_additive [CharP F 2] (e : ℕ → F) (n j : ℕ) (x y : F) :
    (coordinates e n j).eval (x + y) =
      (coordinates e n j).eval x + (coordinates e n j).eval y := by
  induction n generalizing j x y with
  | zero => simp [coordinates]
  | succ n ih =>
    by_cases hj : j = n
    · simp only [coordinates, if_pos hj, unitStep_eval, annihilator_additive, mul_add]
    · rw [coordinates, if_neg hj]
      exact coordinateStep_additive _ _ _ (annihilator_additive e n) (fun a b => ih j a b) x y

/-- The actual coordinate polynomials have the sharp degree bound used by selectors. -/
theorem coordinates_natDegree_le (e : ℕ → F) (n j : ℕ) :
    (coordinates e n j).natDegree ≤ 2 ^ (n - 1) := by
  induction n generalizing j with
  | zero => simp [coordinates]
  | succ n ih =>
    change (coordinates e (n + 1) j).natDegree ≤ 2 ^ n
    by_cases hj : j = n
    · rw [coordinates, if_pos hj]
      exact (unitStep_natDegree_le _ _).trans (annihilator_natDegree_le e n)
    · rw [coordinates, if_neg hj]
      apply (coordinateStep_natDegree_le _ _ _).trans
      apply max_le
      · exact (ih j).trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le n 1))
      · exact annihilator_natDegree_le e n

end NearCubicGates.Adapters.Routing.Coordinates

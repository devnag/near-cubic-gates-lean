import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

/-!
# One triangular coordinate-construction step

The coordinate generator in `lem:generator` uses these generic algebraic
lemmas for its polynomial operations. They construct an annihilator and
coordinate row without assuming the affine-routing theorem.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial

variable {F : Type*} [Field F]

/-- Double the annihilator's root space by adjoining `e`. -/
def annihilatorStep (p : F[X]) (e : F) : F[X] :=
  p ^ 2 + C (p.eval e) * p

/-- A polynomial that is zero at old roots and one at the new basis vector. -/
def unitStep (p : F[X]) (e : F) : F[X] :=
  C (p.eval e)⁻¹ * p

/-- Preserve an old coordinate on old roots and make its value at `e` zero. -/
def coordinateStep (p l : F[X]) (e : F) : F[X] :=
  l + C (l.eval e) * unitStep p e

theorem annihilatorStep_eval (p : F[X]) (e x : F) :
    (annihilatorStep p e).eval x = (p.eval x) ^ 2 + p.eval e * p.eval x := by
  simp [annihilatorStep]

theorem annihilatorStep_eval_zero_iff [CharP F 2] (p : F[X]) (e x : F) :
    (annihilatorStep p e).eval x = 0 ↔ p.eval x = 0 ∨ p.eval x = p.eval e := by
  rw [annihilatorStep_eval]
  have h : (p.eval x) ^ 2 + p.eval e * p.eval x = p.eval x * (p.eval x + p.eval e) := by ring
  rw [h, mul_eq_zero, CharTwo.add_eq_zero]

theorem unitStep_eval (p : F[X]) (e x : F) :
    (unitStep p e).eval x = (p.eval e)⁻¹ * p.eval x := by
  simp [unitStep]

theorem unitStep_eval_self (p : F[X]) (e : F) (hc : p.eval e ≠ 0) :
    (unitStep p e).eval e = 1 := by
  simp [unitStep_eval, hc]

theorem unitStep_eval_at_root (p : F[X]) (e x : F) (hx : p.eval x = 0) :
    (unitStep p e).eval x = 0 := by
  simp [unitStep_eval, hx]

theorem coordinateStep_eval_at_root (p l : F[X]) (e x : F) (hx : p.eval x = 0) :
    (coordinateStep p l e).eval x = l.eval x := by
  simp [coordinateStep, unitStep_eval_at_root p e x hx]

theorem coordinateStep_eval_self [CharP F 2] (p l : F[X]) (e : F) (hc : p.eval e ≠ 0) :
    (coordinateStep p l e).eval e = 0 := by
  simp [coordinateStep, unitStep_eval_self p e hc, CharTwo.add_self_eq_zero]

theorem annihilatorStep_additive [CharP F 2] (p : F[X]) (e : F)
    (hp : ∀ x y : F, p.eval (x + y) = p.eval x + p.eval y) (x y : F) :
    (annihilatorStep p e).eval (x + y) =
      (annihilatorStep p e).eval x + (annihilatorStep p e).eval y := by
  simp only [annihilatorStep_eval, hp, add_pow_char]
  ring

theorem coordinateStep_additive (p l : F[X]) (e : F)
    (hp : ∀ x y : F, p.eval (x + y) = p.eval x + p.eval y)
    (hl : ∀ x y : F, l.eval (x + y) = l.eval x + l.eval y) (x y : F) :
    (coordinateStep p l e).eval (x + y) =
      (coordinateStep p l e).eval x + (coordinateStep p l e).eval y := by
  simp only [coordinateStep, eval_add, eval_mul, eval_C, unitStep_eval, hp, hl]
  ring

/-- The new roots are exactly the old roots and their translate by `e`. -/
theorem annihilatorStep_kernel_translate [CharP F 2] (p : F[X]) (e : F)
    (hp : ∀ x y : F, p.eval (x + y) = p.eval x + p.eval y) (x : F) :
    (annihilatorStep p e).eval x = 0 ↔ p.eval x = 0 ∨ p.eval (x + e) = 0 := by
  rw [annihilatorStep_eval_zero_iff, hp, CharTwo.add_eq_zero]

end NearCubicGates.Adapters.Routing.Coordinates

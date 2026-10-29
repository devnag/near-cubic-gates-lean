import SourceAdapters.Joins.AffineRouting

/-! Normalized selectors have exactly their Boolean guard values on the cube.
The coordinate coefficient array is used literally. No assumptions on
the other variables are needed. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace NearCubicGates.Adapters.Routing.Selectors

open scoped BigOperators
open Polynomial

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem eval_liftX (reads : Vars → F) (p : F[X]) :
    MvPolynomial.eval reads (liftX p) = p.eval (reads none) := by
  unfold liftX
  rw [Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval reads).comp MvPolynomial.C = RingHom.id F := by
    ext x
    simp
  rw [hc]
  simp

omit [CharP F 2] in
theorem eval_coordinate {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)
    (reads : Vars → F) (v : Fin m → Bool) (h : reads none = cubeEval m e v)
    (a : Fin m) :
    MvPolynomial.eval reads (liftX (linearized m (coords.coeff a))) =
      if v a then 1 else 0 := by
  rw [eval_liftX, h, coords.on_cube]

theorem eval_selector {m : ℕ} {e : Fin m → F} (coords : Coordinates m e)
    (p : Pattern m) (reads : Vars → F) (v : Fin m → Bool)
    (h : reads none = cubeEval m e v) :
    MvPolynomial.eval reads (selector coords p) = if patternHolds p v then 1 else 0 := by
  classical
  have hf (a : Fin m) :
      MvPolynomial.eval reads (match p a with
        | none => 1
        | some true => liftX (linearized m (coords.coeff a))
        | some false => 1 + liftX (linearized m (coords.coeff a))) =
        if ∀ b, p a = some b → v a = b then 1 else 0 := by
    cases hp : p a with
    | none => simp
    | some b =>
      cases b <;> cases hv : v a <;>
        simp [eval_coordinate coords reads v h, hv, CharTwo.add_self_eq_zero]
  unfold selector
  rw [map_prod]
  have he : (∏ a : Fin m, MvPolynomial.eval reads (match p a with
        | none => 1
        | some true => liftX (linearized m (coords.coeff a))
        | some false => 1 + liftX (linearized m (coords.coeff a)))) =
      ∏ a : Fin m, (if ∀ b, p a = some b → v a = b then (1 : F) else 0) :=
    Finset.prod_congr rfl (fun a _ => hf a)
  apply he.trans
  by_cases hp : patternHolds p v
  · rw [if_pos hp]
    apply Finset.prod_eq_one
    intro a _
    exact if_pos (hp a)
  · rw [if_neg hp]
    obtain ⟨a, ha⟩ := not_forall.mp hp
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    exact if_neg ha

end NearCubicGates.Adapters.Routing.Selectors

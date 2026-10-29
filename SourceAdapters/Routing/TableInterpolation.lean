import Mathlib.LinearAlgebra.Lagrange

/-!
# Interpolation of an arbitrary table on an injectively labelled Boolean cube

The construction in `thm:embedding`: fill all points of H, then
interpolate the complete table to one polynomial of degree strictly below
|H|=2^m. This generic algebraic helper is independent of the routing join.
It works over finite fields and at m=0, where the cube is the singleton containing zero.
The canonical interpolant is a mathematical witness, not a paid generator.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing.Interpolation

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The field point labelled by a Boolean cube vertex. -/
def cubeValue {m : ℕ} (e : Fin m → F) (v : Fin m → Bool) : F :=
  ∑ i : Fin m, if v i then e i else 0

/-- The canonical Lagrange polynomial for the complete table. -/
def cubeInterpolant {m : ℕ} (e : Fin m → F) (a : F → F) : F[X] :=
  Lagrange.interpolate Finset.univ (cubeValue e) (fun v => a (cubeValue e v))

theorem cubeInterpolant_degree_lt {m : ℕ} (e : Fin m → F)
    (hi : Function.Injective (cubeValue e)) (a : F → F) :
    (cubeInterpolant e a).degree < (2 ^ m : ℕ) := by
  simpa [cubeInterpolant] using
    Lagrange.degree_interpolate_lt (s := Finset.univ) (fun v => a (cubeValue e v)) hi.injOn

theorem cubeInterpolant_eval {m : ℕ} (e : Fin m → F)
    (hi : Function.Injective (cubeValue e)) (a : F → F) (v : Fin m → Bool) :
    (cubeInterpolant e a).eval (cubeValue e v) = a (cubeValue e v) :=
  Lagrange.eval_interpolate_at_node _ hi.injOn (Finset.mem_univ v)

theorem cubeInterpolant_eval_of_mem {m : ℕ} (e : Fin m → F)
    (hi : Function.Injective (cubeValue e)) (a : F → F) (z : F)
    (hz : ∃ v : Fin m → Bool, cubeValue e v = z) :
    (cubeInterpolant e a).eval z = a z := by
  obtain ⟨v, rfl⟩ := hz
  exact cubeInterpolant_eval e hi a v

/-- Exact content of table interpolation, stated without any routing contract. -/
theorem table_interpolation (m : ℕ) (e : Fin m → F)
    (hi : Function.Injective (fun v : Fin m → Bool => ∑ i : Fin m, if v i then e i else 0))
    (a : F → F) :
    ∃ A : F[X], A.degree < (2 ^ m : ℕ) ∧
      ∀ z, (∃ v : Fin m → Bool, (∑ i : Fin m, if v i then e i else 0) = z) → A.eval z = a z :=
  ⟨cubeInterpolant e a, cubeInterpolant_degree_lt e hi a, cubeInterpolant_eval_of_mem e hi a⟩

/-- Dimension zero has one vertex and gives the constant table value. -/
theorem cubeInterpolant_zero (e : Fin 0 → F) (a : F → F) :
    cubeInterpolant e a = C (a 0) := by
  simp [cubeInterpolant, Finset.univ_unique, cubeValue]

end NearCubicGates.Adapters.Routing.Interpolation

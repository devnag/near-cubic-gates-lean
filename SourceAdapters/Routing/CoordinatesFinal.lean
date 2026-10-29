import SourceAdapters.Routing.CoordinatesBasis
import SourceAdapters.Routing.CoordinatesLinearized

/-! # Compact coordinates on every point of an independent Boolean cube

All coefficients are the explicit triangular recurrences. Independence alone
discharges the pivots. Ordinary-machine generation remains a separate theorem.
-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial
open scoped BigOperators
variable {F : Type*} [Field F] [CharP F 2]

theorem coordinates_on_cube (e : ℕ → F) (n : ℕ)
    (hi : Function.Injective (cube e n)) (j : Fin n) (v : Fin n → Bool) :
    (coordinates e n j.val).eval (cube e n v) = if v j then 1 else 0 := by
  classical
  have hz : (coordinates e n j.val).eval 0 = 0 := by
    simpa [CharTwo.add_self_eq_zero] using coordinates_additive e n j.val 0 0
  let h : F →+ F :=
    { toFun := (coordinates e n j.val).eval
      map_zero' := hz
      map_add' := coordinates_additive e n j.val }
  have hb (i : Fin n) : h (e i.val) = if j = i then 1 else 0 := by
    change (coordinates e n j.val).eval (e i.val) = _
    simpa only [Fin.ext_iff] using
      coordinates_on_basis e n (pivot_ne_zero_of_cube_injective e n hi) j.val i.val j.isLt i.isLt
  change h (∑ i : Fin n, if v i then e i.val else 0) = _
  rw [map_sum]
  simp only [apply_ite, map_zero, hb]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

theorem coordinateCoefficients_on_cube (e : ℕ → F) (n : ℕ)
    (hi : Function.Injective (cube e n)) (j : Fin n) (v : Fin n → Bool) :
    (linearizedPolynomial (coordinateCoefficients e n j.val)).eval (cube e n v) =
      if v j then 1 else 0 := by
  rw [coordinateCoefficients_correct]
  exact coordinates_on_cube e n hi j v

theorem coordinateCoefficients_degree (e : ℕ → F) (n j : ℕ) :
    (linearizedPolynomial (coordinateCoefficients e n j)).natDegree ≤ 2 ^ (n - 1) := by
  rw [coordinateCoefficients_correct]
  exact coordinates_natDegree_le e n j

end NearCubicGates.Adapters.Routing.Coordinates

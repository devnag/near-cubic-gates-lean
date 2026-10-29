import SourceAdapters.Routing.CoordinatesFinal

/-! # Explicit coordinate arrays for a finite independent basis -/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial
open scoped BigOperators
variable {F : Type*} [Field F]

def extendBasis {m : ℕ} (e : Fin m → F) (i : ℕ) : F :=
  if hi : i < m then e ⟨i, hi⟩ else 0

theorem cube_extendBasis {m : ℕ} (e : Fin m → F) (v : Fin m → Bool) :
    cube (extendBasis e) m v = ∑ i : Fin m, if v i then e i else 0 := by
  simp [cube, extendBasis]

/-- The full matrix, with exactly m rows and m coefficient positions per row. -/
def finiteCoefficients {m : ℕ} (e : Fin m → F) (j : Fin m) : Fin m → F :=
  coordinateCoefficients (extendBasis e) m j.val

theorem finiteCoefficients_on_cube [CharP F 2] {m : ℕ} (e : Fin m → F)
    (hi : Function.Injective (fun v : Fin m → Bool => ∑ i : Fin m, if v i then e i else 0))
    (j : Fin m) (v : Fin m → Bool) :
    (linearizedPolynomial (finiteCoefficients e j)).eval
      (∑ i : Fin m, if v i then e i else 0) = if v j then 1 else 0 := by
  have he : Function.Injective (cube (extendBasis e) m) := by
    intro v w hvw
    apply hi
    simpa only [cube_extendBasis] using hvw
  simpa only [finiteCoefficients, cube_extendBasis] using
    coordinateCoefficients_on_cube (extendBasis e) m he j v

theorem finiteCoefficients_degree [CharP F 2] {m : ℕ} (e : Fin m → F) (j : Fin m) :
    (linearizedPolynomial (finiteCoefficients e j)).natDegree ≤ 2 ^ (m - 1) := by
  exact coordinateCoefficients_degree (extendBasis e) m j.val

end NearCubicGates.Adapters.Routing.Coordinates

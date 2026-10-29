import SourceAdapters.Joins.AffineRouting
import SourceAdapters.Routing.CoordinatesFinite
import SourceAdapters.Routing.TableInterpolation

/-! # Explicit coordinate and interpolation suppliers for the routing interface

AffineRouting f131eb0d was after producer, reviewer and assembly docks.
The coefficient matrix is the definite triangular recurrence, rather than a
choice from coordinate existence. Its ordinary-machine implementation is separate.
-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing

variable {F : Type} [Field F]

/-- The exact array whose field masks the succinct generator must print. -/
def explicitCoordinates [CharP F 2] {m : ℕ} (e : Fin m → F) (hi : Independent m e) :
    Coordinates m e where
  coeff := Coordinates.finiteCoefficients e
  on_cube := Coordinates.finiteCoefficients_on_cube e hi
  degree_le := Coordinates.finiteCoefficients_degree e

theorem coordinateExistence [CharP F 2] : CoordinateExistence (F := F) := by
  intro m _ e hi
  exact ⟨explicitCoordinates e hi⟩

theorem tableInterpolation : TableInterpolation (F := F) := by
  intro m e hi a
  exact Interpolation.table_interpolation m e hi a

end NearCubicGates.Adapters.Routing

import SourceAdapters.Joins.AffineRouting

/-! Explicit routing catalog coordinates and activation conditions. See `app:affine-embedding`.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Catalog

def itemStage : RoutingItem → ℕ
  | .route j | .switchBit j | .pair j | .column j _ | .dataBit j => j

def hostRole : RoutingItem → ℕ
  | .route _ => 0
  | .switchBit _ => 3
  | .pair _ => 4
  | .column _ _ => 1
  | .dataBit _ => 2

def itemCondition (l : Layout) (i : RoutingItem) (c : ℕ) : Prop :=
  match i with | .column _ t => ColumnCase l.q t c | _ => True

/-- Exactly the stage and carry-index bounds of the emitted list, with no endpoint wrap. -/
def Active (l : Layout) : RoutingItem → Prop
  | .route j | .switchBit j | .pair j => j < switchCount l.k
  | .column j t => j < switchCount l.k ∧ t < l.q
  | .dataBit j => j < 2 * l.k

end NearCubicGates.Adapters.Routing.Catalog

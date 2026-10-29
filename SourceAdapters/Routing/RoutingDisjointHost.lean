import SourceAdapters.Routing.RoutingCatalog
import SourceAdapters.Routing.RoutingPolynomialColumns

/-! Stage, role, and the unique selected carry case identify one routing equation instance. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Catalog

theorem item_eq_of_host (l : Layout) (i j : RoutingItem) (c : ℕ)
    (hs : itemStage i = itemStage j) (hr : hostRole i = hostRole j)
    (hi : itemCondition l i c) (hj : itemCondition l j c) : i = j := by
  cases i <;> cases j <;> simp_all [itemStage, hostRole, itemCondition]
  exact RoutingPolynomial.columnCase_unique hi hj

end NearCubicGates.Adapters.Routing.Catalog

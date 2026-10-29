import SourceAdapters.Routing.SelectorsBounds

/-! Formal weighted degree of every actual routing equation and its emitted sum. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Selectors
variable {F : Type} [Field F]

theorem routingItem_degree (l : Layout) (i : RoutingItem) :
    (i.expr (F := F) l).poly.weightedTotalDegree (weight l.m) ≤ 2 * (l.h - 1) := by
  have hx (b : ℕ) : (MvPolynomial.X (some b) : MP F).weightedTotalDegree (weight l.m) ≤ l.h - 1 := by
    simp [degree_X, weight, Layout.h]
  have hl : l.h - 1 ≤ 2 * (l.h - 1) := by omega
  cases i with
  | route j =>
    apply degree_add
    · exact (degree_add _ (hx _) (hx _)).trans hl
    · simpa only [two_mul, Expr.poly] using degree_mul _ (hx _) (degree_add _ (hx _) (hx _))
  | switchBit j =>
    exact degree_add _ (degree_pow _ (hx _) 2) ((hx _).trans hl)
  | pair j => exact (degree_add _ (hx _) (hx _)).trans hl
  | column j t => exact (degree_add _ (hx _) (hx _)).trans hl
  | dataBit j => exact degree_add _ (degree_pow _ (hx _) 2) ((hx _).trans hl)

theorem routingDegree (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e) :
    (emit coords (routingTerms l)).weightedTotalDegree (weight l.m) ≤
      l.m * 2 ^ (l.m - 1) + 2 * (l.h - 1) := by
  apply degree_emit
  intro t ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  exact routingItem_degree l i

end NearCubicGates.Adapters.Routing.Selectors

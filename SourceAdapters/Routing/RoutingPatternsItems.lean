import SourceAdapters.Routing.RoutingPatternsHost
import SourceAdapters.Routing.RoutingCatalogDefs
import SourceAdapters.Routing.RoutingPolynomialColumns

/-! Exact active-host classification for every routing item. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Patterns

theorem guard_iff (l : Layout) (i : RoutingItem) (hi : Catalog.Active l i)
    (x s c r a : ℕ) (h : InRange l x s c r a) :
    patternHolds (i.guard l) (bits l.m (cellMask l x s c r a)) ↔
      s = Catalog.itemStage i ∧ r = Catalog.hostRole i ∧ a = 0 ∧ Catalog.itemCondition l i c := by
  have hz : 0 < l.C := Nat.two_pow_pos l.q
  have hstage (j : ℕ) (hj : j < switchCount l.k) : j < 2 ^ l.ell := by
    have := l.stages_fit
    unfold switchCount at hj
    omega
  cases i with
  | route j =>
    simpa [RoutingItem.guard, Catalog.itemStage, Catalog.hostRole, Catalog.itemCondition] using
      routePattern_iff l x s c r a j 0 0 0 h (hstage j hi) (by decide) hz hz
  | switchBit j =>
    simpa [RoutingItem.guard, Catalog.itemStage, Catalog.hostRole, Catalog.itemCondition] using
      routePattern_iff l x s c r a j 3 0 0 h (hstage j hi) (by decide) hz hz
  | pair j =>
    simpa [RoutingItem.guard, Catalog.itemStage, Catalog.hostRole, Catalog.itemCondition] using
      routePattern_iff l x s c r a j 4 0 0 h (hstage j hi) (by decide) hz hz
  | column j t =>
    obtain ⟨hj, ht⟩ := hi
    have hv : 2 ^ t - 1 < l.C := by
      have hp := Nat.two_pow_pos t
      have hh : 2 ^ t ≤ l.C := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt ht)
      omega
    have hk : (if t + 1 < l.q then 2 ^ (t + 1) - 1 else 2 ^ t - 1) < l.C := by
      split_ifs with hn
      · have hp := Nat.two_pow_pos (t + 1)
        have hh : 2 ^ (t + 1) ≤ l.C := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hn)
        omega
      · exact hv
    have hh := routePattern_iff l x s c r a j 1
      (if t + 1 < l.q then 2 ^ (t + 1) - 1 else 2 ^ t - 1) (2 ^ t - 1)
      h (hstage j hj) (by decide) hk hv
    rw [RoutingPolynomial.column_mask_iff l.q t c ht] at hh
    simpa only [RoutingItem.guard, Catalog.itemStage, Catalog.hostRole, Catalog.itemCondition,
      and_assoc, and_left_comm, and_comm] using hh
  | dataBit j =>
    have hj : j < 2 ^ l.ell := lt_of_lt_of_le hi l.stages_fit
    simpa [RoutingItem.guard, Catalog.itemStage, Catalog.hostRole, Catalog.itemCondition] using
      routePattern_iff l x s c r a j 2 0 0 h hj (by decide) hz hz

end NearCubicGates.Adapters.Routing.Patterns

import SourceAdapters.Routing.RoutingDisjointHost
import SourceAdapters.Routing.RoutingPatternsItems
import SourceAdapters.Routing.RoutingPatternsCover

/-! Full indexed noncancellation for the emitted routing-term list. See `thm:embedding`. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing

theorem active_guard_unique (l : Layout) (i j : RoutingItem)
    (hi : Catalog.Active l i) (hj : Catalog.Active l j) (v : Fin l.m → Bool)
    (hgi : patternHolds (i.guard l) v) (hgj : patternHolds (j.guard l) v) : i = j := by
  obtain ⟨x, s, c, r, a, hin, hbits⟩ := Patterns.cube_bits_cell l v
  rw [← hbits] at hgi hgj
  obtain ⟨hsi, hri, _, hci⟩ := (Patterns.guard_iff l i hi x s c r a hin).mp hgi
  obtain ⟨hsj, hrj, _, hcj⟩ := (Patterns.guard_iff l j hj x s c r a hin).mp hgj
  exact Catalog.item_eq_of_host l i j c (hsi.symm.trans hsj) (hri.symm.trans hrj) hci hcj

variable {F : Type} [Field F]

/-- Distinct LIST INDICES cannot select two routing equations at the same cube point. -/
theorem routingTerms_disjoint (l : Layout) : DisjointTerms (routingTerms (F := F) l) := by
  intro i j hne v hboth
  let ii : Fin (routingItems l).length := ⟨i.val, by
    simpa only [routingTerms, List.length_map] using i.isLt⟩
  let jj : Fin (routingItems l).length := ⟨j.val, by
    simpa only [routingTerms, List.length_map] using j.isLt⟩
  have hi : Catalog.Active l ((routingItems l).get ii) :=
    (Catalog.mem_routingItems_iff l _).mp (List.get_mem _ _)
  have hj : Catalog.Active l ((routingItems l).get jj) :=
    (Catalog.mem_routingItems_iff l _).mp (List.get_mem _ _)
  have hgi : patternHolds (((routingItems l).get ii).guard l) v := by
    have hh := hboth.1
    change patternHolds ((routingTerms (F := F) l)[i.val]).guard v at hh
    simpa only [routingTerms, List.getElem_map, List.get_eq_getElem] using hh
  have hgj : patternHolds (((routingItems l).get jj).guard l) v := by
    have hh := hboth.2
    change patternHolds ((routingTerms (F := F) l)[j.val]).guard v at hh
    simpa only [routingTerms, List.getElem_map, List.get_eq_getElem] using hh
  have he := active_guard_unique l _ _ hi hj v hgi hgj
  have hij : ii = jj := (List.nodup_iff_injective_get.mp (Catalog.nodup_routingItems l)) he
  apply hne
  exact Fin.ext (congrArg (fun z : Fin (routingItems l).length => z.val) hij)

end NearCubicGates.Adapters.Routing

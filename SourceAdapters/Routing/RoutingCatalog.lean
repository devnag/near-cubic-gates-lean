import SourceAdapters.Routing.RoutingCatalogDefs
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! Exact finite routing catalog and absence of duplicate equation instances. See `app:affine-embedding`.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Catalog

theorem mem_routingItems_iff (l : Layout) (i : RoutingItem) :
    i ∈ routingItems l ↔ Active l i := by
  cases i <;> simp [routingItems, Active, List.mem_flatMap]

theorem itemStage_lt (l : Layout) (i : RoutingItem) (hi : Active l i) : itemStage i < 2 ^ l.ell := by
  have hs := l.stages_fit
  cases i <;> simp only [Active, itemStage, switchCount] at * <;> omega

theorem hostRole_lt (i : RoutingItem) : hostRole i < 8 := by
  cases i <;> simp [hostRole]

/-- One switch stage has three fixed-role checks followed by its carry cases. -/
def stageItems (q j : ℕ) : List RoutingItem :=
  [.route j, .switchBit j, .pair j] ++ (List.range q).map (.column j)

theorem mem_stageItems_iff (q j : ℕ) (i : RoutingItem) : i ∈ stageItems q j ↔
    i = .route j ∨ i = .switchBit j ∨ i = .pair j ∨ ∃ t < q, i = .column j t := by
  simp [stageItems, eq_comm]

theorem stage_of_mem_stageItems {q j : ℕ} {i : RoutingItem} (hi : i ∈ stageItems q j) : itemStage i = j := by
  rcases (mem_stageItems_iff q j i).mp hi with rfl | rfl | rfl | ⟨t, _, rfl⟩ <;> rfl

theorem nodup_stageItems (q j : ℕ) : (stageItems q j).Nodup := by
  have hm : ((List.range q).map (RoutingItem.column j)).Nodup :=
    List.Nodup.map (fun _ _ h => RoutingItem.column.inj h |>.2) (List.nodup_range (n := q))
  simpa [stageItems] using hm

theorem nodup_routingItems (l : Layout) : (routingItems l).Nodup := by
  have hstage : ((List.range (switchCount l.k)).flatMap (stageItems l.q)).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro j _
      exact nodup_stageItems l.q j
    · apply (List.nodup_range (n := switchCount l.k)).imp
      intro j j' hne i hi hi'
      exact hne ((stage_of_mem_stageItems hi).symm.trans (stage_of_mem_stageItems hi'))
  have hdata : ((List.range (2 * l.k)).map RoutingItem.dataBit).Nodup :=
    List.Nodup.map (fun _ _ h => RoutingItem.dataBit.inj h) (List.nodup_range (n := 2 * l.k))
  change (((List.range (switchCount l.k)).flatMap (stageItems l.q)) ++
    (List.range (2 * l.k)).map RoutingItem.dataBit).Nodup
  apply List.Nodup.append hstage hdata
  intro i hi hi'
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hi
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hi'
  simp [stageItems] at hj

end NearCubicGates.Adapters.Routing.Catalog

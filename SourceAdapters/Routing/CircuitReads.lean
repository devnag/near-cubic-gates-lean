import SourceAdapters.Routing.CircuitSupport
import SourceAdapters.Routing.LayoutBank

/-! Fixed routing expression reads and counts; LayoutBank supplies the existing stage/dimension facts. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit

 theorem role_reads (l : Layout) :
    eta l 1 ∈ globalBank l ∧ eta l 2 ∈ globalBank l ∧
    (eta l 3 ^^^ eta l 1) ∈ globalBank l ∧ (eta l 4 ^^^ eta l 1) ∈ globalBank l := by
  simp [globalBank, routingBank]

 theorem pair_read (l : Layout) (j : ℕ) :
    (eta l 4 ^^^ eta l 1 ^^^ 2 ^ dimension l.k j) ∈ globalBank l := by
  have hm := List.mem_map_of_mem
    (f := fun d => eta l 4 ^^^ eta l 1 ^^^ 2 ^ d)
    (List.mem_range.mpr (LayoutFacts.dimension_lt l j))
  simp only [globalBank, routingBank, List.mem_append]
  aesop

 theorem column_read (l : Layout) (t : ℕ) (ht : t < l.q) : columnCarry l t ∈ globalBank l := by
  have hm := List.mem_map_of_mem (f := columnCarry l) (List.mem_range.mpr ht)
  simp only [globalBank, routingBank, List.mem_append]
  aesop

variable {F : Type}

theorem route_reads (l : Layout) (j : ℕ) (hj : j < switchCount l.k) :
    ReadsIn (globalBank l) ((RoutingItem.route j).expr l : Expr F) := by
  have hs := LayoutFacts.stage_mem_globalBank l j hj
  have hz := LayoutFacts.zero_mem_globalBank l
  have hr := (role_reads l).1
  simpa only [RoutingItem.expr, ReadsIn] using And.intro (And.intro hz hs.1) (And.intro hr (And.intro hs.1 hs.2))

theorem switchBit_reads (l : Layout) (j : ℕ) :
    ReadsIn (globalBank l) ((RoutingItem.switchBit j).expr l : Expr F) := by
  exact ⟨(role_reads l).2.2.1, (role_reads l).2.2.1⟩

theorem pair_reads (l : Layout) (j : ℕ) :
    ReadsIn (globalBank l) ((RoutingItem.pair j).expr l : Expr F) :=
  ⟨(role_reads l).2.2.2, pair_read l j⟩

theorem column_reads (l : Layout) (j t : ℕ) (ht : t < l.q) :
    ReadsIn (globalBank l) ((RoutingItem.column j t).expr l : Expr F) :=
  ⟨LayoutFacts.zero_mem_globalBank l, column_read l t ht⟩

theorem dataBit_reads (l : Layout) (j : ℕ) :
    ReadsIn (globalBank l) ((RoutingItem.dataBit j).expr l : Expr F) :=
  ⟨(role_reads l).2.1, (role_reads l).2.1⟩

theorem routingItems_reads (l : Layout) :
    ∀ t ∈ routingItems l, ReadsIn (globalBank l) (t.expr l : Expr F) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, hj, ht⟩ := List.mem_flatMap.mp ht
    have hj' := List.mem_range.mp hj
    rcases List.mem_append.mp ht with ht | ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact route_reads l j hj'
      · exact switchBit_reads l j
      · exact pair_reads l j
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
      exact column_reads l j r (List.mem_range.mp hr)
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    exact dataBit_reads l j

theorem routingItem_size (l : Layout) (t : RoutingItem) : gateCount (t.expr l : Expr F) ≤ 9 := by
  cases t <;> simp [RoutingItem.expr, gateCount]

theorem routingItems_length (l : Layout) :
    (routingItems l).length = switchCount l.k * (3 + l.q) + 2 * l.k := by
  simp only [routingItems, List.length_append, List.length_flatMap, List.length_cons, List.length_nil, List.length_map, List.length_range]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range]

theorem routingItems_length_le (l : Layout) : (routingItems l).length ≤ 2 * l.k * (l.q + 4) := by
  rw [routingItems_length]
  unfold switchCount
  calc
    _ ≤ (2 * l.k) * (3 + l.q) + 2 * l.k :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le (2 * l.k) 1)) _
    _ = _ := by ring

end NearCubicGates.Adapters.Routing.Circuit
end

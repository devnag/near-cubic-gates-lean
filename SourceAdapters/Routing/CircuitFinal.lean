import SourceAdapters.Routing.CircuitReads

/-! Complete generic normalized-term compiler correctness theorem and routing circuit supplier. See `app:affine-embedding`, `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing
open NearCubicGates.Adapters.ACSP
variable {F : Type} [Field F]

namespace Circuit

/-- Generic compiler correctness: syntactic bank reads, actual shared prefix, exact polynomial, and paid gate count.
This theorem concerns the finite circuit, not an ordinary-machine runtime. -/
theorem compileTerms_correct (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (items : List (Item l.m F)) (hr : ∀ item ∈ items, ReadsIn (globalBank l) item.2) :
    Supports (globalBank l) (emit coords (termList items)) ∧
    WellFormedCircuit ((globalBank l).length + 1) (compileTerms l e coords items) ∧
    (compileTerms l e coords items).poly ((globalBank l).length + 1) =
      MvPolynomial.rename (encodeVar l) (emit coords (termList items)) ∧
    (compileTerms l e coords items).size ≤
      3 * l.m ^ 2 + 2 * l.m + 1 + (2 * l.m + 3) * items.length +
        (items.map (fun t => gateCount t.2)).sum :=
  ⟨compileTerms_support l coords items hr, compileTerms_spec l coords items hr⟩

end Circuit

/-- The exact routing circuit constructor satisfies every field of CircuitCorrect.
No independence or characteristic-two premise is needed for circuit compilation itself. -/
theorem circuitCorrect (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e) :
    CircuitCorrect l e coords := by
  let items : List (Circuit.Item l.m F) := (routingItems l).map fun t => (t.guard l, t.expr l)
  have hr : ∀ item ∈ items, Circuit.ReadsIn (globalBank l) item.2 := by
    intro item hi
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi
    exact Circuit.routingItems_reads l t ht
  have ht : Circuit.termList items = routingTerms (F := F) l := by
    simp only [Circuit.termList, items, List.map_map, Function.comp_def, routingTerms]
  have he : compileRouting l e coords = Circuit.compileTerms l e coords items := Circuit.compileRouting_eq l e coords
  have h := Circuit.compileTerms_correct l coords items hr
  rw [ht] at h
  refine ⟨?_, ?_, ?_, ?_, Circuit.routingItems_length_le l⟩
  · intro v hv b hb
    subst v
    exact h.1 (some b) hv
  · rw [he]
    exact h.2.1
  · rw [he]
    exact h.2.2.1
  · have hg : ∀ ts : List RoutingItem,
        (ts.map fun t => Circuit.gateCount (t.expr l : Expr F)).sum ≤ 9 * ts.length := by
      intro ts
      induction ts with
      | nil => simp
      | cons t ts ih =>
          have hb := Circuit.routingItem_size (F := F) l t
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
    have hg' : (items.map (fun t => Circuit.gateCount t.2)).sum ≤ 9 * items.length := by
      simpa only [items, List.map_map, Function.comp_def, List.length_map] using hg (routingItems l)
    have hl : items.length = (routingItems l).length := by simp only [items, List.length_map]
    rw [he]
    have hs := h.2.2.2
    unfold circuitBound
    rw [hl] at hs hg'
    nlinarith

end NearCubicGates.Adapters.Routing
end

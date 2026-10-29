import SourceAdapters.Routing.CircuitPattern

/-! Shared-prefix compiler for arbitrary normalized guard/equation pairs. See `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP
variable {F : Type} [Field F]

abbrev Item (m : ℕ) (F : Type) := Pattern m × Expr F

def termList {m : ℕ} (items : List (Item m F)) : List (Term m F) :=
  items.map fun item => ⟨item.1, item.2.poly⟩

def itemPoly {m : ℕ} {e : Fin m → F} (coords : Coordinates m e) (item : Item m F) : MP F :=
  selector coords item.1 * item.2.poly

def itemCost {m : ℕ} (item : Item m F) : ℕ :=
  3 + ((List.finRange m).map (patternCost item.1)).sum + gateCount item.2

def termStep (l : Layout) (ids : List ℕ) (item : Item l.m F) (acc : ℕ) : Builder F ℕ := do
  let guard ← compilePattern ids item.1
  let equation ← compileExpr l item.2
  let term ← pushGate (.mul guard equation)
  pushGate (.add acc term)

def compileTerms (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e)
    (items : List (Item l.m F)) : ArithCircuit F :=
  ⟨((do
    let ids ← compileCoordinates coords
    let acc ← pushGate (.const 0)
    loop (termStep l ids) items acc : Builder F ℕ).run []).2⟩

theorem termStep_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ids : List ℕ) (item : Item l.m F) (hr : ReadsIn (globalBank l) item.2)
    (gs : Gates F) (hw : WF ((globalBank l).length + 1) gs)
    (hc : Refs ((globalBank l).length + 1) gs ids ((List.finRange l.m).map (coordPoly l coords)))
    (acc : ℕ) (v : Poly ((globalBank l).length + 1) F) (ha : Has ((globalBank l).length + 1) gs acc v) :
    Produces ((globalBank l).length + 1) gs ((termStep l ids item acc).run gs)
      (v + MvPolynomial.rename (encodeVar l) (itemPoly coords item)) (itemCost item) := by
  let rp := (compilePattern ids item.1).run gs
  have hp := compilePattern_spec l coords ids item.1 gs hw hc
  let re := (compileExpr l item.2).run rp.2
  have he := compileExpr_spec l item.2 hr rp.2 hp.ext.wf
  have hpat := hp.has.mono he.ext.initial
  have hac := ha.mono (hp.ext.initial.trans he.ext.initial)
  let g1 := re.2 ++ [ArithGate.mul rp.1 re.1]
  have ht : Ext ((globalBank l).length + 1) re.2 g1 :=
    ⟨List.prefix_append _ _, wf_push he.ext.wf _ ⟨hpat.1, he.has.1⟩⟩
  have hmul : Has ((globalBank l).length + 1) g1 re.2.length
      (MvPolynomial.rename (encodeVar l) (itemPoly coords item)) := by
    simpa only [itemPoly, map_mul] using has_mul hpat he.has
  have hac' := hac.mono ht.initial
  have hf : Ext ((globalBank l).length + 1) g1 (g1 ++ [.add acc re.2.length]) :=
    ⟨List.prefix_append _ _, wf_push ht.wf _ ⟨hac'.1, hmul.1⟩⟩
  change Produces _ gs (g1.length, g1 ++ [.add acc re.2.length]) _ _
  refine ⟨hp.ext.trans (he.ext.trans (ht.trans hf)), has_add hac' hmul, ?_, by simp⟩
  have hpl := hp.length_eq
  have hel := he.length_eq
  change rp.2.length = _ at hpl
  change re.2.length = _ at hel
  simp only [g1, List.length_append, List.length_singleton, itemCost]
  omega

theorem termLoop_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ids : List ℕ) (items : List (Item l.m F)) (hr : ∀ item ∈ items, ReadsIn (globalBank l) item.2)
    (gs : Gates F) (hw : WF ((globalBank l).length + 1) gs)
    (hc : Refs ((globalBank l).length + 1) gs ids ((List.finRange l.m).map (coordPoly l coords)))
    (acc : ℕ) (v : Poly ((globalBank l).length + 1) F)
    (ha : Has ((globalBank l).length + 1) gs acc v) (hlast : acc + 1 = gs.length) :
    Produces ((globalBank l).length + 1) gs ((loop (termStep l ids) items acc).run gs)
      (v + MvPolynomial.rename (encodeVar l) ((items.map (itemPoly coords)).sum))
      (items.map itemCost).sum := by
  induction items generalizing gs acc v with
  | nil =>
      change Produces _ gs (acc, gs) (v + MvPolynomial.rename (encodeVar l) 0) 0
      simpa only [map_zero, add_zero] using
        (⟨Ext.refl hw, ha, by simp, hlast⟩ : Produces _ gs (acc, gs) v 0)
  | cons item items ih =>
      let st := (termStep l ids item acc).run gs
      have hs := termStep_spec l coords ids item (hr item (by simp)) gs hw hc acc v ha
      have hh := ih (fun t ht => hr t (by simp [ht])) st.2 hs.ext.wf
        (hc.mono hs.ext.initial) st.1 _ hs.has hs.last
      change Produces _ gs ((loop (termStep l ids) items st.1).run st.2) _ _
      refine ⟨hs.ext.trans hh.ext, ?_, ?_, hh.last⟩
      · simpa only [List.map_cons, List.sum_cons, map_add, add_assoc] using hh.has
      · have h1 := hs.length_eq
        have h2 := hh.length_eq
        change st.2.length = _ at h1
        simp only [List.map_cons, List.sum_cons]
        omega

omit [Field F] in
theorem itemCost_sum_le (l : Layout) (items : List (Item l.m F)) :
    (items.map itemCost).sum ≤ (2 * l.m + 3) * items.length + (items.map (fun t => gateCount t.2)).sum := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have hp := patternCost_sum_le item.1 (List.finRange l.m)
      simp only [List.length_finRange] at hp
      simp only [List.map_cons, List.sum_cons, List.length_cons, itemCost]
      nlinarith

theorem has_last_poly {n i : ℕ} {gs : Gates F} {p : Poly n F}
    (h : Has n gs i p) (hlast : i + 1 = gs.length) : (ArithCircuit.mk gs).poly n = p := by
  change (values n gs).getLastD 0 = p
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, values_length]
  have he : gs.length - 1 = i := by omega
  rw [he]
  exact h.2

theorem compileTerms_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (items : List (Item l.m F)) (hr : ∀ item ∈ items, ReadsIn (globalBank l) item.2) :
    WellFormedCircuit ((globalBank l).length + 1) (compileTerms l e coords items) ∧
    (compileTerms l e coords items).poly ((globalBank l).length + 1) =
      MvPolynomial.rename (encodeVar l) (emit coords (termList items)) ∧
    (compileTerms l e coords items).size ≤
      3 * l.m ^ 2 + 2 * l.m + 1 + (2 * l.m + 3) * items.length +
        (items.map (fun t => gateCount t.2)).sum := by
  let cr := (compileCoordinates coords).run ([] : Gates F)
  have hco := compileCoordinates_spec l coords [] (by intro i; exact Fin.elim0 i)
  let g1 := cr.2 ++ [ArithGate.const (0 : F)]
  have he : Ext ((globalBank l).length + 1) cr.2 g1 :=
    ⟨List.prefix_append _ _, wf_push hco.1.wf _ trivial⟩
  have hz : Has ((globalBank l).length + 1) g1 cr.2.length 0 := by
    simpa only [map_zero] using has_const (n := (globalBank l).length + 1) cr.2 (0 : F)
  have hs := termLoop_spec l coords cr.1 items hr g1 he.wf
    (hco.2.1.mono he.initial) cr.2.length 0 hz (by simp [g1])
  have heq : compileTerms l e coords items =
      ⟨((loop (termStep l cr.1) items cr.2.length).run g1).2⟩ := rfl
  rw [heq]
  refine ⟨hs.ext.wf, ?_, ?_⟩
  · have hh := has_last_poly hs.has hs.last
    unfold itemPoly at hh
    simpa only [zero_add, emit, termList, List.map_map, Function.comp_def] using hh
  · have h1 := hco.2.2
    have h2 := hs.length_eq
    have hb := itemCost_sum_le l items
    change cr.2.length = _ at h1
    change ((loop (termStep l cr.1) items cr.2.length).run g1).2.length ≤ _
    simp only [List.length_nil, zero_add] at h1
    rw [h2]
    simp only [g1, List.length_append, List.length_singleton, h1]
    omega

/-- The routing constructor is exactly the generic shared-prefix constructor. -/
theorem compileRouting_eq (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e) :
    compileRouting l e coords = compileTerms l e coords
      ((routingItems l).map fun t => (t.guard l, t.expr l)) := by
  unfold compileRouting compileTerms termStep
  simp only [← forIn_eq_loop, List.forIn_map, bind_assoc, bind_pure]

end NearCubicGates.Adapters.Routing.Circuit
end

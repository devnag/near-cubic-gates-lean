import Proof.Wire_3_5.ListMachineRowRadixClass
import Proof.Wire_3_5.ListMachineFilter
import Proof.Wire_3_5.FinalPassFiltBlock

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly pone pmul psum eval_pmul eval_psum eval_pone eval_congr_atoms)
open NearCubicWires.WireExponent3_5.FinalPass

/-! ## One parity -/

/-- The parity `⊕_k c_k Z_{o+k}` as a linear polynomial. -/
def linPolyFrom : ℕ → List Bool → Poly
  | _, [] => []
  | o, b :: cs => (if b then [[o]] else []) ++ linPolyFrom (o + 1) cs

/-- A parity from coordinate `0`. -/
def linPoly (c : List Bool) : Poly := linPolyFrom 0 c

theorem eval_linPolyFrom (ρ : ℕ → Bool) : ∀ (c : List Bool) (o : ℕ) (Z : List Bool), c.length ≤ Z.length →
    (∀ k < c.length, ρ (o + k) = Z.getD k false) → F2Poly.eval (linPolyFrom o c) ρ = Filt.parityDot c Z
  | [], _, _, _, _ => by simp [linPolyFrom, Filt.parityDot]
  | b :: cs, o, [], h, _ => by simp at h
  | b :: cs, o, z :: zs, h, hρ => by
    have ih := eval_linPolyFrom ρ cs (o + 1) zs (by simpa using h) (fun k hk => by
      have := hρ (k + 1) (by simp; omega); simpa [show o + (k + 1) = o + 1 + k by ring] using this)
    have h0 : ρ o = z := by simpa using hρ 0 (by simp)
    rw [linPolyFrom, eval_append, ih, Filt.parityDot]
    cases b <;> simp [eval_cons, h0]

theorem linPolyFrom_size : ∀ (c : List Bool) (o : ℕ), DegLe (linPolyFrom o c) 1 ∧ AtomsLt (linPolyFrom o c) (o + c.length)
  | [], _ => ⟨by simp [linPolyFrom, DegLe], by simp [linPolyFrom, AtomsLt]⟩
  | b :: cs, o => by
    obtain ⟨h1, h2⟩ := linPolyFrom_size cs (o + 1)
    refine ⟨fun m hm => ?_, fun m hm i hi => ?_⟩
    · simp only [linPolyFrom, List.mem_append] at hm
      rcases hm with hm | hm
      · cases b <;> simp_all
      · exact h1 m hm
    · simp only [linPolyFrom, List.mem_append] at hm
      rcases hm with hm | hm
      · cases b <;> simp_all
      · have := h2 m hm i hi; simp; omega

/-! ## A visit and the table -/

/-- One visited base seed accepts: at most `32` of its parities are one. -/
def visitPoly (vs : List (List Bool)) : Poly := symPolyRef (fun k => decide (k ≤ 32)) vs.length (vs.map linPoly)

/-- **The regular filter from its table**: at least `thr` of the visits accept. -/
def tabPoly (thr : ℕ) (tbl : List (List (List Bool))) : Poly :=
  symPolyRef (fun k => decide (thr ≤ k)) tbl.length (tbl.map visitPoly)

theorem trueCount_le_length (ls : List Poly) (ρ : ℕ → Bool) : trueCount ls ρ ≤ ls.length := by
  unfold trueCount; exact List.length_filter_le _ _

theorem trueCount_map {α : Type} (l : List α) (g : α → Poly) (ρ : ℕ → Bool) (q : α → Bool)
    (h : ∀ a ∈ l, F2Poly.eval (g a) ρ = q a) : trueCount (l.map g) ρ = (l.filter q).length := by
  unfold trueCount
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro a ha
  simp [Function.comp, h a ha]

theorem eval_visitPoly (vs : List (List Bool)) (Z : List Bool) (hv : ∀ cs ∈ vs, cs.length ≤ Z.length) :
    F2Poly.eval (visitPoly vs) (fun i => Z.getD i false) = Filt.visitOk vs Z := by
  unfold visitPoly
  rw [symPolyRef_eval _ _ _ _ (by have := trueCount_le_length (vs.map linPoly) (fun i => Z.getD i false); simpa using this)]
  rw [trueCount_map vs linPoly _ (fun c => Filt.parityDot c Z) (fun c hc =>
    eval_linPolyFrom _ c 0 Z (hv c hc) (fun k _ => by simp))]
  rfl

/-- **The table's filter on every point.** -/
theorem eval_tabPoly (thr : ℕ) (tbl : List (List (List Bool))) (Z : List Bool)
    (hv : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ Z.length) :
    F2Poly.eval (tabPoly thr tbl) (fun i => Z.getD i false) = Filt.tabEval thr tbl Z := by
  unfold tabPoly
  rw [symPolyRef_eval _ _ _ _ (by have := trueCount_le_length (tbl.map visitPoly) (fun i => Z.getD i false); simpa using this)]
  rw [trueCount_map tbl visitPoly _ (fun vs => Filt.visitOk vs Z) (fun vs hvs => eval_visitPoly vs Z (hv vs hvs))]
  rfl

theorem visitPoly_size (vs : List (List Bool)) (L V : ℕ) (hv : ∀ cs ∈ vs, cs.length ≤ L) (hV : vs.length ≤ V) :
    DegLe (visitPoly vs) V ∧ AtomsLt (visitPoly vs) L := by
  have h := symPolyRef_size (fun k => decide (k ≤ 32)) vs.length L 1 (vs.map linPoly)
    (fun b hb => by obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb; exact (linPolyFrom_size c 0).1)
    (fun b hb => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      have := (linPolyFrom_size c 0).2
      intro m hm i hi; have := this m hm i hi; have := hv c hc; omega)
  exact ⟨h.1.mono (by omega), h.2⟩

theorem tabPoly_size (thr : ℕ) (tbl : List (List (List Bool))) (L V : ℕ) (hv : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L)
    (hV : ∀ vs ∈ tbl, vs.length ≤ V) : DegLe (tabPoly thr tbl) (V * tbl.length) ∧ AtomsLt (tabPoly thr tbl) L :=
  symPolyRef_size _ tbl.length L V (tbl.map visitPoly)
    (fun b hb => by obtain ⟨vs, hvs, rfl⟩ := List.mem_map.mp hb; exact (visitPoly_size vs L V (hv vs hvs) (hV vs hvs)).1)
    (fun b hb => by obtain ⟨vs, hvs, rfl⟩ := List.mem_map.mp hb; exact (visitPoly_size vs L V (hv vs hvs) (hV vs hvs)).2)

/-! ## The witness over the corners -/

/-- The filter's witness over the CORNER atoms: every coordinate replaced by its corner form `Z^±`. -/
def filtWit (thr : ℕ) (tbl : List (List (List Bool))) (sgn : Bool) : Poly := psubst (tabPoly thr tbl) (cornerPoly sgn)

theorem filtWit_deg (thr : ℕ) (tbl : List (List (List Bool))) (sgn : Bool) (L V : ℕ)
    (hv : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L) (hV : ∀ vs ∈ tbl, vs.length ≤ V) :
    DegLe (filtWit thr tbl sgn) (3 * (V * tbl.length)) :=
  psubst_deg _ _ _ 3 (tabPoly_size thr tbl L V hv hV).1 (cornerPoly_deg sgn)

theorem filtWit_atoms (thr : ℕ) (tbl : List (List (List Bool))) (sgn : Bool) (L V : ℕ)
    (hv : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L) (hV : ∀ vs ∈ tbl, vs.length ≤ V) :
    AtomsLt (filtWit thr tbl sgn) (4 * L) :=
  psubst_atoms' _ _ L (4 * L) (tabPoly_size thr tbl L V hv hV).2
    (fun q hq m hm i hi => by have := cornerPoly_atoms sgn q m hm i hi; omega)

theorem filt_witness (thr : ℕ) (tbl : List (List (List Bool))) (L : ℕ) (hv : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L)
    (sgn : Bool) (X : List Bool) (hX : X.length = 4 * L) :
    Filt.tabEval thr tbl (Pop.popBits sgn X) = F2Poly.eval (filtWit thr tbl sgn) fun i => X.getD i false := by
  have hZ := Pop.popBits_length sgn L X hX
  rw [← eval_tabPoly thr tbl (Pop.popBits sgn X) (fun vs hvs cs hcs => by rw [hZ]; exact hv vs hvs cs hcs), filtWit,
    eval_psubst]
  apply eval_congr_atoms (tabPoly_size thr tbl L (tbl.map List.length).sum hv (fun vs hvs =>
    List.le_sum_of_mem (List.mem_map_of_mem hvs))).2
  intro q hq
  rw [eval_cornerPoly]
  have hq' : q < (Pop.popBits sgn X).length := by rw [hZ]; exact hq
  rw [List.getD_eq_getElem _ _ hq', Pop.popBits_getElem sgn L X hX q hq]
  congr 1
  funext k
  rw [List.getD_eq_getElem _ _ (by have := k.isLt; omega)]

end NearCubicWires.WireExponent3_5.ListMachine.Row

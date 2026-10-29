import SourceAdapters.Routing.CircuitSemantics

/-! Exact expression compiler correctness theorem, including syntactic read validity and gate count. See `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP
variable {F : Type} [Field F]

def gateCount : Expr F → ℕ
  | .const _ | .read _ => 1
  | .add a b | .mul a b => gateCount a + gateCount b + 1
  | .square a => gateCount a + 1

def ReadsIn (bank : List ℕ) : Expr F → Prop
  | .const _ => True
  | .read v => match v with | none => True | some b => b ∈ bank
  | .add a b | .mul a b => ReadsIn bank a ∧ ReadsIn bank b
  | .square a => ReadsIn bank a

structure Produces (n : ℕ) (gs : Gates F) (r : ℕ × Gates F) (p : Poly n F) (cost : ℕ) : Prop where
  ext : Ext n gs r.2
  has : Has n r.2 r.1 p
  length_eq : r.2.length = gs.length + cost
  last : r.1 + 1 = r.2.length

omit [Field F] in
 theorem readIndex_lt (l : Layout) (v : Vars)
    (h : match v with | none => True | some b => b ∈ globalBank l) :
    readIndex l v < (globalBank l).length + 1 := by
  cases v with
  | none => simp [readIndex]
  | some b =>
      have hi := List.idxOf_lt_length_iff.mpr h
      simp only [readIndex]
      omega

omit [Field F] in
 theorem encodeVar_val (l : Layout) (v : Vars)
    (h : match v with | none => True | some b => b ∈ globalBank l) :
    (encodeVar l v).val = readIndex l v := by
  exact Nat.min_eq_left (by have := readIndex_lt l v h; omega)

theorem push_produces {n : ℕ} {gs : Gates F} (hw : WF n gs) (g : ArithGate F)
    (hg : GateOK n gs.length g) :
    Produces n gs ((pushGate g).run gs) (g.poly n (values n gs)) 1 :=
  ⟨(push_spec hw g hg).1, (push_spec hw g hg).2.1, (push_spec hw g hg).2.2, by simp⟩

theorem compileExpr_spec (l : Layout) (E : Expr F) (hr : ReadsIn (globalBank l) E)
    (gs : Gates F) (hw : WF ((globalBank l).length + 1) gs) :
    Produces ((globalBank l).length + 1) gs ((compileExpr l E).run gs)
      (MvPolynomial.rename (encodeVar l) E.poly) (gateCount E) := by
  induction E generalizing gs with
  | const c =>
      simpa only [compileExpr, Expr.poly, gateCount, MvPolynomial.rename_C, ArithGate.poly] using
        push_produces hw (.const c) trivial
  | read v =>
      have hi := readIndex_lt l v hr
      have he := encodeVar_val l v hr
      have hx : (⟨readIndex l v, hi⟩ : Fin ((globalBank l).length + 1)) = encodeVar l v :=
        Fin.ext he.symm
      simpa only [compileExpr, Expr.poly, gateCount, MvPolynomial.rename_X, ArithGate.poly,
        dif_pos hi, hx] using push_produces hw (.input (readIndex l v)) hi
  | add a b ia ib =>
      let ra := (compileExpr l a).run gs
      have ha := ia hr.1 gs hw
      let rb := (compileExpr l b).run ra.2
      have hb := ib hr.2 ra.2 ha.ext.wf
      have hpa := ha.has.mono hb.ext.initial
      have hx := push_produces hb.ext.wf (.add ra.1 rb.1) ⟨hpa.1, hb.has.1⟩
      change Produces _ gs (rb.2.length, rb.2 ++ [.add ra.1 rb.1]) _ _
      refine ⟨ha.ext.trans (hb.ext.trans hx.ext), ?_, ?_, by simp⟩
      · simpa only [Expr.poly, map_add] using has_add hpa hb.has
      · have hla := ha.length_eq
        have hlb := hb.length_eq
        change ra.2.length = _ at hla
        change rb.2.length = _ at hlb
        simp only [List.length_append, List.length_singleton, gateCount]
        omega
  | mul a b ia ib =>
      let ra := (compileExpr l a).run gs
      have ha := ia hr.1 gs hw
      let rb := (compileExpr l b).run ra.2
      have hb := ib hr.2 ra.2 ha.ext.wf
      have hpa := ha.has.mono hb.ext.initial
      have hx := push_produces hb.ext.wf (.mul ra.1 rb.1) ⟨hpa.1, hb.has.1⟩
      change Produces _ gs (rb.2.length, rb.2 ++ [.mul ra.1 rb.1]) _ _
      refine ⟨ha.ext.trans (hb.ext.trans hx.ext), ?_, ?_, by simp⟩
      · simpa only [Expr.poly, map_mul] using has_mul hpa hb.has
      · have hla := ha.length_eq
        have hlb := hb.length_eq
        change ra.2.length = _ at hla
        change rb.2.length = _ at hlb
        simp only [List.length_append, List.length_singleton, gateCount]
        omega
  | square a ia =>
      let ra := (compileExpr l a).run gs
      have ha := ia hr gs hw
      have hx := push_produces ha.ext.wf (.mul ra.1 ra.1) ⟨ha.has.1, ha.has.1⟩
      change Produces _ gs (ra.2.length, ra.2 ++ [.mul ra.1 ra.1]) _ _
      refine ⟨ha.ext.trans hx.ext, ?_, ?_, by simp⟩
      · simpa only [Expr.poly, map_pow, pow_two, map_mul] using has_mul ha.has ha.has
      · have hla := ha.length_eq
        change ra.2.length = _ at hla
        simp only [List.length_append, List.length_singleton, gateCount]
        omega

end NearCubicGates.Adapters.Routing.Circuit
end

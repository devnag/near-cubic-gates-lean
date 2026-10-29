import SourceAdapters.Routing.CircuitExpr
import Mathlib.Data.List.Forall2

/-! Shared-reference lists and the three-gate coefficient accumulator. See `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP
variable {F : Type} [Field F]

abbrev Refs (n : ℕ) (gs : Gates F) (ids : List ℕ) (ps : List (Poly n F)) : Prop :=
  List.Forall₂ (Has n gs) ids ps

theorem Refs.mono {n : ℕ} {gs gs' : Gates F} {ids : List ℕ} {ps : List (Poly n F)}
    (h : Refs n gs ids ps) (he : gs <+: gs') : Refs n gs' ids ps :=
  h.imp (fun _ _ hp => hp.mono he)

theorem Refs.getD {n : ℕ} {gs : Gates F} {ids : List ℕ} {ps : List (Poly n F)}
    (h : Refs n gs ids ps) (i : ℕ) (hi : i < ps.length) (d : ℕ) (z : Poly n F) :
    Has n gs (ids.getD i d) (ps.getD i z) := by
  have hids : i < ids.length := by rw [h.length_eq]; exact hi
  simpa only [List.getD_eq_getElem _ _ hids, List.getD_eq_getElem _ _ hi, List.get_eq_getElem] using h.get hids hi

def coeffStep {α : Type} (coeff : α → F) (index : α → ℕ) (r : α) (acc : ℕ) : Builder F ℕ := do
  let c ← pushGate (.const (coeff r))
  let term ← pushGate (.mul c (index r))
  pushGate (.add acc term)

theorem coeffStep_spec {α : Type} {n : ℕ} (coeff : α → F) (index : α → ℕ) (r : α)
    (gs : Gates F) (hw : WF n gs) (acc : ℕ) (p q : Poly n F)
    (hp : Has n gs acc p) (hq : Has n gs (index r) q) :
    Produces n gs ((coeffStep coeff index r acc).run gs) (p + MvPolynomial.C (coeff r) * q) 3 := by
  let g1 := gs ++ [ArithGate.const (coeff r)]
  have e1 : Ext n gs g1 := ⟨List.prefix_append _ _, wf_push hw _ trivial⟩
  have hc : Has n g1 gs.length (MvPolynomial.C (coeff r)) := has_const gs _
  have hq1 := hq.mono e1.initial
  let g2 := g1 ++ [ArithGate.mul gs.length (index r)]
  have e2 : Ext n g1 g2 := ⟨List.prefix_append _ _, wf_push e1.wf _ ⟨hc.1, hq1.1⟩⟩
  have ht : Has n g2 g1.length (MvPolynomial.C (coeff r) * q) := has_mul hc hq1
  have hp2 := hp.mono (e1.initial.trans e2.initial)
  have e3 : Ext n g2 (g2 ++ [.add acc g1.length]) :=
    ⟨List.prefix_append _ _, wf_push e2.wf _ ⟨hp2.1, ht.1⟩⟩
  change Produces n gs (g2.length, g2 ++ [.add acc g1.length]) _ 3
  exact ⟨e1.trans (e2.trans e3), has_add hp2 ht, by simp [g2, g1], by simp⟩

theorem coeffLoop_spec {α : Type} {n : ℕ} (coeff : α → F) (index : α → ℕ)
    (term : α → Poly n F) (rs : List α) (gs : Gates F) (hw : WF n gs)
    (acc : ℕ) (p : Poly n F) (hp : Has n gs acc p) (hlast : acc + 1 = gs.length)
    (ht : ∀ r ∈ rs, Has n gs (index r) (term r)) :
    Produces n gs ((loop (coeffStep coeff index) rs acc).run gs)
      (p + (rs.map fun r => MvPolynomial.C (coeff r) * term r).sum) (3 * rs.length) := by
  induction rs generalizing gs acc p with
  | nil =>
      simpa only [loop, List.map_nil, List.sum_nil, add_zero, List.length_nil, mul_zero,
        StateT.run, pure, StateT.pure] using
        (⟨Ext.refl hw, hp, by simp, hlast⟩ : Produces n gs (acc, gs) p 0)
  | cons r rs ih =>
      let step := (coeffStep coeff index r acc).run gs
      have hs := coeffStep_spec coeff index r gs hw acc p (term r) hp (ht r (by simp))
      have hh := ih step.2 hs.ext.wf step.1 _ hs.has hs.last
        (fun u hu => (ht u (by simp [hu])).mono hs.ext.initial)
      change Produces n gs ((loop (coeffStep coeff index) rs step.1).run step.2) _ _
      refine ⟨hs.ext.trans hh.ext, ?_, ?_, hh.last⟩
      · simpa only [List.map_cons, List.sum_cons, add_assoc] using hh.has
      · have h1 := hs.length_eq
        have h2 := hh.length_eq
        change step.2.length = gs.length + 3 at h1
        simp only [List.length_cons]
        omega

end NearCubicGates.Adapters.Routing.Circuit
end

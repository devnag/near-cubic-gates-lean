import SourceAdapters.Routing.CircuitCoordinates

/-! Actual normalized selector compiler over retained coordinate references. See `app:affine-embedding`, `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP
open scoped BigOperators
variable {F : Type} [Field F]

def patternCost {m : ℕ} (p : Pattern m) (a : Fin m) : ℕ :=
  match p a with | none => 0 | some true => 1 | some false => 2

def factor {m n : ℕ} (p : Pattern m) (co : Fin m → Poly n F) (a : Fin m) : Poly n F :=
  match p a with | none => 1 | some true => co a | some false => 1 + co a

def patternStep {m : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ) (a : Fin m) (acc : ℕ) : Builder F ℕ := do
  match p a with
  | none => pure acc
  | some b =>
      let coord := ids.getD a.val one
      let f ← if b then pure coord else pushGate (.add one coord)
      pushGate (.mul acc f)

theorem patternStep_spec {m n : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ) (a : Fin m)
    (co : Fin m → Poly n F) (acc : ℕ) (v : Poly n F) (gs : Gates F) (hw : WF n gs)
    (h1 : Has n gs one 1) (hc : Has n gs (ids.getD a.val one) (co a))
    (ha : Has n gs acc v) (hlast : acc + 1 = gs.length) :
    Produces n gs ((patternStep ids p one a acc).run gs) (v * factor p co a) (patternCost p a) := by
  cases hp : p a with
  | none =>
      simp only [patternStep, hp, factor, patternCost]
      change Produces n gs (acc, gs) (v * 1) 0
      simpa only [mul_one] using
        (⟨Ext.refl hw, ha, by simp, hlast⟩ : Produces n gs (acc, gs) v 0)
  | some b =>
      cases b with
      | true =>
          have hs := push_produces hw (.mul acc (ids.getD a.val one)) ⟨ha.1, hc.1⟩
          simp only [patternStep, hp, factor, patternCost]
          change Produces n gs ((pushGate (.mul acc (ids.getD a.val one))).run gs) (v * co a) 1
          simpa only [ArithGate.poly, ha.2, hc.2] using hs
      | false =>
          let g1 := gs ++ [ArithGate.add one (ids.getD a.val one)]
          have he : Ext n gs g1 := ⟨List.prefix_append _ _, wf_push hw _ ⟨h1.1, hc.1⟩⟩
          have hf : Has n g1 gs.length (1 + co a) := has_add h1 hc
          have ha' := ha.mono he.initial
          have hs := push_produces he.wf (.mul acc gs.length) ⟨ha'.1, hf.1⟩
          have hr : Produces n gs (g1.length, g1 ++ [.mul acc gs.length]) (v * (1 + co a)) 2 :=
            ⟨he.trans hs.ext, has_mul ha' hf, by simp [g1], by simp⟩
          simp only [patternStep, hp, factor, patternCost]
          exact hr

theorem patternLoop_spec {m n : ℕ} (ids : List ℕ) (p : Pattern m) (one : ℕ)
    (co : Fin m → Poly n F) (as : List (Fin m)) (acc : ℕ) (v : Poly n F)
    (gs : Gates F) (hw : WF n gs) (h1 : Has n gs one 1)
    (hc : ∀ a ∈ as, Has n gs (ids.getD a.val one) (co a))
    (ha : Has n gs acc v) (hlast : acc + 1 = gs.length) :
    Produces n gs ((loop (patternStep ids p one) as acc).run gs)
      (v * (as.map (factor p co)).prod) (as.map (patternCost p)).sum := by
  induction as generalizing acc v gs with
  | nil =>
      change Produces n gs (acc, gs) (v * 1) 0
      simpa only [mul_one] using
        (⟨Ext.refl hw, ha, by simp, hlast⟩ : Produces n gs (acc, gs) v 0)
  | cons a as ih =>
      let st := (patternStep ids p one a acc).run gs
      have hs := patternStep_spec ids p one a co acc v gs hw h1 (hc a (by simp)) ha hlast
      have hh := ih st.1 (v * factor p co a) st.2 hs.ext.wf (h1.mono hs.ext.initial)
        (fun b hb => (hc b (by simp [hb])).mono hs.ext.initial) hs.has hs.last
      change Produces n gs ((loop (patternStep ids p one) as st.1).run st.2) _ _
      refine ⟨hs.ext.trans hh.ext, ?_, ?_, hh.last⟩
      · simpa only [List.map_cons, List.prod_cons, mul_assoc] using hh.has
      · have h2 := hh.length_eq
        have hst := hs.length_eq
        change st.2.length = _ at hst
        simp only [List.map_cons, List.sum_cons]
        omega

theorem compilePattern_eq {m : ℕ} (ids : List ℕ) (p : Pattern m) :
    (compilePattern ids p : Builder F ℕ) = (do
      let one ← pushGate (.const 1)
      loop (patternStep ids p one) (List.finRange m) one) := by
  unfold compilePattern patternStep
  simp only [← forIn_eq_loop, pure_bind, bind_pure]
  congr 1
  funext one
  congr 1
  funext a acc
  cases hp : p a with
  | none => simp only [pure_bind]
  | some b => cases b <;> simp

theorem rename_selector (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e) (p : Pattern l.m) :
    MvPolynomial.rename (encodeVar l) (selector coords p) =
      ∏ a : Fin l.m, factor p (coordPoly l coords) a := by
  rw [selector, map_prod]
  apply Finset.prod_congr rfl
  intro a _
  cases hp : p a with
  | none => simp only [hp, factor, map_one]
  | some b => cases b <;> simp only [hp, factor, coordPoly, map_add, map_one]

theorem patternCost_sum_le {m : ℕ} (p : Pattern m) (as : List (Fin m)) :
    (as.map (patternCost p)).sum ≤ 2 * as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have hc : patternCost p a ≤ 2 := by
        unfold patternCost
        cases p a with
        | none => decide
        | some b => cases b <;> decide
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem compilePattern_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ids : List ℕ) (p : Pattern l.m) (gs : Gates F)
    (hw : WF ((globalBank l).length + 1) gs)
    (hc : Refs ((globalBank l).length + 1) gs ids ((List.finRange l.m).map (coordPoly l coords))) :
    Produces ((globalBank l).length + 1) gs ((compilePattern ids p).run gs)
      (MvPolynomial.rename (encodeVar l) (selector coords p))
      (1 + ((List.finRange l.m).map (patternCost p)).sum) := by
  let g1 := gs ++ [ArithGate.const (1 : F)]
  have he : Ext ((globalBank l).length + 1) gs g1 :=
    ⟨List.prefix_append _ _, wf_push hw _ trivial⟩
  have h1 : Has ((globalBank l).length + 1) g1 gs.length 1 := by
    simpa only [map_one] using has_const (n := (globalBank l).length + 1) gs (1 : F)
  have hcoords : ∀ a ∈ List.finRange l.m,
      Has ((globalBank l).length + 1) g1 (ids.getD a.val gs.length) (coordPoly l coords a) := by
    intro a _
    have h := (hc.mono he.initial).getD a.val (by simpa only [List.length_map, List.length_finRange] using a.isLt)
      gs.length 0
    simpa using h
  have hs := patternLoop_spec ids p gs.length (coordPoly l coords) (List.finRange l.m)
    gs.length 1 g1 he.wf h1 hcoords h1 (by simp [g1])
  rw [compilePattern_eq]
  change Produces _ gs ((loop (patternStep ids p gs.length) (List.finRange l.m) gs.length).run g1) _ _
  refine ⟨he.trans hs.ext, ?_, ?_, hs.last⟩
  · simpa only [one_mul, ← Fin.prod_univ_def, ← rename_selector] using hs.has
  · calc
      _ = g1.length + ((List.finRange l.m).map (patternCost p)).sum := hs.length_eq
      _ = gs.length + (1 + ((List.finRange l.m).map (patternCost p)).sum) := by
        simp only [g1, List.length_append, List.length_singleton, Nat.add_assoc]

end NearCubicGates.Adapters.Routing.Circuit
end

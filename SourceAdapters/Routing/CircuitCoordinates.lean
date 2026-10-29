import SourceAdapters.Routing.CircuitPowers

/-! Actual shared coordinate-array circuit, preserving the supplied coefficient array. See `lem:generator`. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP Polynomial
open scoped BigOperators
variable {F : Type} [Field F]

def coordPoly (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e) (a : Fin l.m) :
    Poly ((globalBank l).length + 1) F :=
  MvPolynomial.rename (encodeVar l) (liftX (linearized l.m (coords.coeff a)))

theorem coordPoly_eq (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e) (a : Fin l.m) :
    coordPoly l coords a = ∑ r : Fin l.m,
      MvPolynomial.C (coords.coeff a r) * (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) ^ (2 ^ r.val) := by
  simp [coordPoly, linearized, liftX, Polynomial.eval₂_finsetSum, map_sum, encodeVar, readIndex]

def coordinateRow (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x : ℕ) (a : Fin l.m) : Builder F ℕ := do
  let acc ← pushGate (.const 0)
  loop (coeffStep (coords.coeff a) (fun r => ps.getD r.val x)) (List.finRange l.m) acc

def coordinateStep (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x : ℕ) (a : Fin l.m) (outputs : List ℕ) : Builder F (List ℕ) := do
  let acc ← coordinateRow l coords ps x a
  return outputs ++ [acc]

theorem coordinateRow_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x : ℕ) (a : Fin l.m) (gs : Gates F)
    (hw : WF ((globalBank l).length + 1) gs)
    (hp : Refs ((globalBank l).length + 1) gs ps
      (powers (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) l.m)) :
    Produces ((globalBank l).length + 1) gs ((coordinateRow l coords ps x a).run gs)
      (coordPoly l coords a) (3 * l.m + 1) := by
  let g1 := gs ++ [ArithGate.const (0 : F)]
  have he : Ext ((globalBank l).length + 1) gs g1 :=
    ⟨List.prefix_append _ _, wf_push hw _ trivial⟩
  have hzero : Has ((globalBank l).length + 1) g1 gs.length 0 := by
    simpa only [map_zero] using has_const (n := (globalBank l).length + 1) gs (0 : F)
  have hrs : ∀ r ∈ List.finRange l.m,
      Has ((globalBank l).length + 1) g1 (ps.getD r.val x)
        (MvPolynomial.X (0 : Fin ((globalBank l).length + 1)) ^ (2 ^ r.val)) := by
    intro r _
    have h := (hp.mono he.initial).getD r.val (by simpa only [powers_length] using r.isLt) x 0
    simpa only [powers_getD _ r.isLt] using h
  have hs := coeffLoop_spec (coords.coeff a) (fun r => ps.getD r.val x)
    (fun r : Fin l.m => MvPolynomial.X (0 : Fin ((globalBank l).length + 1)) ^ (2 ^ r.val))
    (List.finRange l.m) g1 he.wf gs.length 0 hzero (by simp [g1]) hrs
  change Produces _ gs ((loop _ (List.finRange l.m) gs.length).run g1) _ _
  refine ⟨he.trans hs.ext, ?_, ?_, hs.last⟩
  · simpa only [zero_add, ← Fin.sum_univ_def, ← coordPoly_eq] using hs.has
  · calc
      _ = g1.length + 3 * l.m := by simpa only [List.length_finRange] using hs.length_eq
      _ = gs.length + (3 * l.m + 1) := by simp [g1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem coordinateLoop_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (ps : List ℕ) (x : ℕ) (as : List (Fin l.m)) (outputs : List ℕ)
    (old : List (Poly ((globalBank l).length + 1) F)) (gs : Gates F)
    (hw : WF ((globalBank l).length + 1) gs)
    (hp : Refs ((globalBank l).length + 1) gs ps
      (powers (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) l.m))
    (ho : Refs ((globalBank l).length + 1) gs outputs old) :
    let result := (loop (coordinateStep l coords ps x) as outputs).run gs
    Ext ((globalBank l).length + 1) gs result.2 ∧
      Refs ((globalBank l).length + 1) result.2 result.1 (old ++ as.map (coordPoly l coords)) ∧
      result.2.length = gs.length + (3 * l.m + 1) * as.length := by
  induction as generalizing outputs old gs with
  | nil =>
      change Ext _ gs gs ∧ Refs _ gs outputs (old ++ []) ∧ gs.length = gs.length + _ * 0
      exact ⟨Ext.refl hw, by simpa using ho, by omega⟩
  | cons a as ih =>
      let row := (coordinateRow l coords ps x a).run gs
      have hr := coordinateRow_spec l coords ps x a gs hw hp
      have ho' : Refs ((globalBank l).length + 1) row.2 (outputs ++ [row.1]) (old ++ [coordPoly l coords a]) :=
        List.rel_append (ho.mono hr.ext.initial) (.cons hr.has .nil)
      have hh := ih (outputs ++ [row.1]) (old ++ [coordPoly l coords a]) row.2 hr.ext.wf
        (hp.mono hr.ext.initial) ho'
      change Ext _ gs ((loop (coordinateStep l coords ps x) as (outputs ++ [row.1])).run row.2).2 ∧
        Refs _ ((loop (coordinateStep l coords ps x) as (outputs ++ [row.1])).run row.2).2
          ((loop (coordinateStep l coords ps x) as (outputs ++ [row.1])).run row.2).1
          (old ++ (a :: as).map (coordPoly l coords)) ∧
        ((loop (coordinateStep l coords ps x) as (outputs ++ [row.1])).run row.2).2.length =
          gs.length + (3 * l.m + 1) * (a :: as).length
      refine ⟨hr.ext.trans hh.1, ?_, ?_⟩
      · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using hh.2.1
      · have h1 := hr.length_eq
        have h2 := hh.2.2
        change row.2.length = _ at h1
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega

theorem compileCoordinates_eq (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e) :
    compileCoordinates coords = (do
      let x ← pushGate (.input 0)
      let ps ← loop (powerStep x) (List.range (l.m - 1)) [x]
      loop (coordinateStep l coords ps x) (List.finRange l.m) []) := by
  unfold compileCoordinates coordinateStep coordinateRow powerStep coeffStep
  simp only [← forIn_eq_loop, bind_assoc, pure_bind, bind_pure]

/-- Exact semantics and count of the shared prefix, after any well-formed earlier gates. -/
theorem compileCoordinates_spec (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (gs : Gates F) (hw : WF ((globalBank l).length + 1) gs) :
    let result := (compileCoordinates coords).run gs
    Ext ((globalBank l).length + 1) gs result.2 ∧
      Refs ((globalBank l).length + 1) result.2 result.1
        ((List.finRange l.m).map (coordPoly l coords)) ∧
      result.2.length = gs.length + (3 * l.m ^ 2 + 2 * l.m) := by
  have hm : 1 ≤ l.m := by simp only [Layout.m]; omega
  let g1 := gs ++ [ArithGate.input 0]
  have he : Ext ((globalBank l).length + 1) gs g1 :=
    ⟨List.prefix_append _ _, wf_push hw _ (by simp [GateOK])⟩
  have hx : Has ((globalBank l).length + 1) g1 gs.length
      (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) := by
    simpa [ArithGate.poly, g1] using
      has_push (n := (globalBank l).length + 1) gs (.input 0)
  have hp0 : Refs ((globalBank l).length + 1) g1 [gs.length]
      (powers (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) [gs.length].length) := by
    simpa [powers] using List.Forall₂.cons hx List.Forall₂.nil
  let pr := (loop (powerStep gs.length) (List.range (l.m - 1)) [gs.length]).run g1
  obtain ⟨hpe, hpl, hpr, hpg⟩ := powerLoop_spec
    (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) gs.length
    (List.range (l.m - 1)) [gs.length] g1 he.wf (by simp) hp0
  have hm' : [gs.length].length + (List.range (l.m - 1)).length = l.m := by simp; omega
  have hpr' : Refs ((globalBank l).length + 1) pr.2 pr.1
      (powers (MvPolynomial.X (0 : Fin ((globalBank l).length + 1))) l.m) := by
    simpa only [hm'] using hpr
  have ho := coordinateLoop_spec l coords pr.1 gs.length (List.finRange l.m) [] [] pr.2 hpe.wf hpr' .nil
  rw [compileCoordinates_eq l coords]
  change Ext _ gs ((loop (coordinateStep l coords pr.1 gs.length) (List.finRange l.m) []).run pr.2).2 ∧
    Refs _ ((loop (coordinateStep l coords pr.1 gs.length) (List.finRange l.m) []).run pr.2).2
      ((loop (coordinateStep l coords pr.1 gs.length) (List.finRange l.m) []).run pr.2).1
      ((List.finRange l.m).map (coordPoly l coords)) ∧
    ((loop (coordinateStep l coords pr.1 gs.length) (List.finRange l.m) []).run pr.2).2.length =
      gs.length + (3 * l.m ^ 2 + 2 * l.m)
  refine ⟨he.trans (hpe.trans ho.1), by simpa only [List.nil_append] using ho.2.1, ?_⟩
  have h1 : pr.2.length = gs.length + l.m := by
    change pr.2.length = _ at hpg
    simp only [g1, List.length_append, List.length_singleton, List.length_range] at hpg
    omega
  have h2 := ho.2.2
  simp only [List.length_finRange] at h2
  rw [h2, h1]
  ring

end NearCubicGates.Adapters.Routing.Circuit
end

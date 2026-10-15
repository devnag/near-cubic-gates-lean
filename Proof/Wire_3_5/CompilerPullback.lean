import Proof.Wire_3_5.CompilerSubstitute
import Proof.Wire_3_5.StarSelection

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

variable {n : ℕ} {ZL ZR : Type}

structure HalfCoords (n : ℕ) (ZL ZR : Type) where
  side : Fin n → Bool
  φL : ZL → Fin n → Bool
  φR : ZR → Fin n → Bool

/-- The original input at the column `(z_L, z_R)`. -/
def HalfCoords.point (C : HalfCoords n ZL ZR) (zl : ZL) (zr : ZR) : BitInput n :=
  fun i => if C.side i then C.φL zl i else C.φR zr i

def pullChild (C : HalfCoords n ZL ZR) (e : ExactThresholdGate n) : SeparatedEquation ZL ZR :=
  ⟨fun zl => -e.target + ∑ i, if C.side i then e.weight i * bitZ (C.φL zl i) else 0,
   fun zr => ∑ i, if C.side i then 0 else e.weight i * bitZ (C.φR zr i)⟩

/-- The pulled-back child holds exactly where the original child holds at the original input. -/
theorem pullChild_holds (C : HalfCoords n ZL ZR) (e : ExactThresholdGate n) (zl : ZL) (zr : ZR) :
    (pullChild C e).holds zl zr = e.eval (C.point zl zr) := by
  unfold pullChild SeparatedEquation.holds ExactThresholdGate.eval HalfCoords.point
  apply decide_eq_decide.mpr
  have hsum : (∑ i, if C.side i then e.weight i * bitZ (C.φL zl i) else 0) +
      (∑ i, if C.side i then 0 else e.weight i * bitZ (C.φR zr i)) =
      ∑ i, e.weight i * if (if C.side i then C.φL zl i else C.φR zr i) then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : C.side i <;> simp [h, bitZ]
  constructor
  · intro h; linarith
  · intro h; linarith

def pullbackChildren (C : HalfCoords n ZL ZR) {g : NormalizedThresholdGate n} (D : ExactDecomposition g) :
    List (SeparatedEquation ZL ZR) :=
  D.children.map (pullChild C)

theorem sum_bitZ_of_count_le_one {β : Type} (L : List β) (f : β → Bool) (h : (L.filter f).length ≤ 1) :
    (L.map fun b => bitZ (f b)).sum = bitZ (L.any f) := by
  induction L with
  | nil => simp [bitZ]
  | cons b L ih =>
    by_cases hb : f b = true
    · have h0 : (L.filter f).length = 0 := by
        simp only [List.filter_cons, hb, if_true, List.length_cons] at h; omega
      have hany : L.any f = false := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
        simp only [List.any_eq_false]; intro x hx; simpa using h0 x hx
      simp only [List.map_cons, List.sum_cons, List.any_cons, hb, Bool.true_or]
      rw [ih (by omega), hany]; simp [bitZ]
    · have h' : (L.filter f).length ≤ 1 := by simpa [List.filter_cons, hb] using h
      simp only [List.map_cons, List.sum_cons, List.any_cons]
      rw [ih h']; simp at hb; simp [hb, bitZ]

theorem pullback_exact (C : HalfCoords n ZL ZR) {g : NormalizedThresholdGate n} (D : ExactDecomposition g)
    (zl : ZL) (zr : ZR) :
    bitZ (g.strictEval (C.point zl zr)) = ((pullbackChildren C D).map fun E => bitZ (E.holds zl zr)).sum := by
  unfold pullbackChildren
  rw [List.map_map]
  have : ((fun E : SeparatedEquation ZL ZR => bitZ (E.holds zl zr)) ∘ pullChild C) =
      fun e => bitZ (e.eval (C.point zl zr)) := by funext e; simp [Function.comp, pullChild_holds]
  rw [this, sum_bitZ_of_count_le_one D.children (fun e => e.eval (C.point zl zr)) (D.disjoint _),
    D.equivalent]

/-! ## Numbering the children of a list of atoms as one pool -/

/-- The label offset of atom `i`: the number of children of the atoms before it. -/
def labelOffset (L : List (List (SeparatedEquation ZL ZR))) (i : ℕ) : ℕ := ((L.take i).map List.length).sum

/-- The child labels of atom `i`: `[offset, offset + #children)`. -/
def labelChildren (L : List (List (SeparatedEquation ZL ZR))) (i : ℕ) : List ℕ :=
  List.range' (labelOffset L i) (L.getD i []).length

/-- The equation of a child label: the flattened pool. -/
def labelEqs (L : List (List (SeparatedEquation ZL ZR))) (dflt : SeparatedEquation ZL ZR) (c : ℕ) :
    SeparatedEquation ZL ZR := L.flatten.getD c dflt

theorem getD_flatten_offset (L : List (List (SeparatedEquation ZL ZR))) (dflt : SeparatedEquation ZL ZR)
    (i j : ℕ) (hj : j < (L.getD i []).length) :
    L.flatten.getD (labelOffset L i + j) dflt = (L.getD i []).getD j dflt := by
  induction L generalizing i with
  | nil => simp at hj
  | cons A L ih =>
    cases i with
    | zero =>
      simp only [labelOffset, List.take_zero, List.map_nil, List.sum_nil, zero_add, List.flatten_cons]
      simp only [List.getD_cons_zero] at hj ⊢
      rw [List.getD_append _ _ _ _ hj]
    | succ i =>
      simp only [List.getD_cons_succ] at hj ⊢
      simp only [labelOffset, List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons] at ih ⊢
      rw [Nat.add_assoc]
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact ih i hj

theorem sum_map_eq_range_getD {β : Type} (l : List β) (d : β) (g : β → ℤ) :
    (l.map g).sum = ((List.range l.length).map fun j => g (l.getD j d)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.getD_cons_zero]
    rw [ih]
    congr 1

/-- **The pool numbering is exact** for atoms that carry exact children: the compiler's `ExactChildren` holds. -/
theorem labelChildren_exact (L : List (List (SeparatedEquation ZL ZR))) (dflt : SeparatedEquation ZL ZR)
    (ρ : ℕ → Bool) (zl : ZL) (zr : ZR)
    (hL : ∀ i, bitZ (ρ i) = ((L.getD i []).map fun E => bitZ (E.holds zl zr)).sum) :
    ExactChildren (labelChildren L) (fun c => (labelEqs L dflt c).holds zl zr) ρ := by
  intro i
  rw [hL i, sum_map_eq_range_getD (L.getD i []) dflt]
  unfold labelChildren labelEqs
  rw [List.range'_eq_map_range, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp]
  rw [getD_flatten_offset L dflt i j (List.mem_range.mp hj)]

/-- The corner of a star at `(u, v)` as half coordinates: left coordinates from the left center half (xor the left
error), right coordinates from the right center half (xor the right error). `corner` selects `c+u+v`, `c+u`, `c+v`, `c`. -/
def starCoords (P : StarParams) (u v : P.Errors) (useU useV : Bool) :
    HalfCoords P.n (P.SideL → Bool) (P.SideR → Bool) where
  side := P.centerSide
  φL := fun xL i => if h : P.centerSide i = true then
      xor (xL ⟨i, h⟩) (useU && P.errorVector P.leftBlock u i) else false
  φR := fun xR i => if h : P.centerSide i = true then false else
      xor (xR ⟨i, h⟩) (useV && P.errorVector P.rightBlock v i)

theorem starCoords_point (P : StarParams) (u v : P.Errors) (useU useV : Bool) (c : BitInput P.n) :
    (starCoords P u v useU useV).point (P.leftPart c) (P.rightPart c) =
      fun i => xor (xor (c i) (useU && P.errorVector P.leftBlock u i)) (useV && P.errorVector P.rightBlock v i) := by
  funext i
  have hL := congrFun (P.leftPart_errorVector_right v)
  have hR := congrFun (P.rightPart_errorVector_left u)
  unfold HalfCoords.point starCoords
  by_cases h : P.centerSide i = true
  · have hv : P.errorVector P.rightBlock v i = false := hL ⟨i, h⟩
    simp [h, hv, StarParams.leftPart]
  · have hu : P.errorVector P.leftBlock u i = false := hR ⟨i, h⟩
    simp [h, hu, StarParams.rightPart]

/-- **The four star corners** `c+u+v`, `c+u`, `c+v`, `c` (the points of `star:delta`'s mixed difference) are the
pullback points of `starCoords` at the center halves. -/
theorem starCoords_corners (P : StarParams) (u v : P.Errors) (c : BitInput P.n) :
    (starCoords P u v true true).point (P.leftPart c) (P.rightPart c) =
        xorInput (xorInput c (P.errorVector P.leftBlock u)) (P.errorVector P.rightBlock v) ∧
      (starCoords P u v true false).point (P.leftPart c) (P.rightPart c) = xorInput c (P.errorVector P.leftBlock u) ∧
      (starCoords P u v false true).point (P.leftPart c) (P.rightPart c) = xorInput c (P.errorVector P.rightBlock v) ∧
      (starCoords P u v false false).point (P.leftPart c) (P.rightPart c) = c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [starCoords_point] <;> funext i <;> simp [xorInput]

end NearCubicWires.WireExponent3_5.Compiler

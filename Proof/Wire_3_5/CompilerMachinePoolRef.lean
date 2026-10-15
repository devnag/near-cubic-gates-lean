import Proof.MachineModel.Semantics

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.CompilerSemantics NearCubicWires.RepairRepresentation

/-- A coordinate record: its center bit's side (`true` = left), its flip bit, its weight. -/
abbrev Coord := Bool × Bool × ℤ

/-- `w·x` with `x = c ⊕ f` is `(if f then w else 0) + flipW f w · c`. -/
def flipW (f : Bool) (w : ℤ) : ℤ := if f then -w else w

def routeL (cs : List Coord) : List ℤ := (cs.filter fun c => c.1).map fun c => flipW c.2.1 c.2.2

/-- The right center-coordinate weights. -/
def routeR (cs : List Coord) : List ℤ := (cs.filter fun c => !c.1).map fun c => flipW c.2.1 c.2.2

/-- The constant moved by the flips: `Σ_{f_i} w_i`. -/
def flipSum (cs : List Coord) : ℤ := (cs.map fun c => if c.2.1 then c.2.2 else 0).sum

/-- `Σ_j L_j·[bit k+j of a]`. -/
def lfk (k : ℕ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | w :: L, a => (if a.testBit k then w else 0) + lfk (k + 1) L a

/-- The side and flip of a coordinate record. -/
def sf (c : Coord) : Bool × Bool := (c.1, c.2.1)

/-- The pulled-back original input bits, in coordinate order, from `(side, flip)` records: a left coordinate reads
the next left center bit of `a_L` (its rank among the left coordinates, counted from `kL`), xored with its flip;
likewise on the right. -/
def pointList (aL aR : ℕ) : List (Bool × Bool) → ℕ → ℕ → List Bool
  | [], _, _ => []
  | c :: cs, kL, kR =>
    if c.1 then xor (aL.testBit kL) c.2 :: pointList aL aR cs (kL + 1) kR
    else xor (aR.testBit kR) c.2 :: pointList aL aR cs kL (kR + 1)

theorem pointList_length (aL aR : ℕ) :
    ∀ (cs : List (Bool × Bool)) (kL kR : ℕ), (pointList aL aR cs kL kR).length = cs.length
  | [], _, _ => rfl
  | c :: cs, kL, kR => by
    unfold pointList
    split_ifs <;> simp [pointList_length aL aR cs]

/-- The original score `Σ_i w_i x_i` at the pulled-back point. -/
def origScore (cs : List Coord) (xs : List Bool) : ℤ :=
  ((cs.zip xs).map fun p => if p.2 then p.1.2.2 else 0).sum

theorem flip_term (f b : Bool) (w : ℤ) :
    (if xor b f then w else 0) = (if f then w else 0) + (if b then flipW f w else 0) := by
  cases f <;> cases b <;> simp [flipW]

/-- **The original score splits** into the flipped constant and the two center-coordinate linear forms. -/
theorem origScore_eq (aL aR : ℕ) : ∀ (cs : List Coord) (kL kR : ℕ),
    origScore cs (pointList aL aR (cs.map sf) kL kR) = flipSum cs + lfk kL (routeL cs) aL + lfk kR (routeR cs) aR
  | [], _, _ => by simp [origScore, pointList, flipSum, routeL, routeR, lfk]
  | c :: cs, kL, kR => by
    have ih1 := origScore_eq aL aR cs (kL + 1) kR
    have ih2 := origScore_eq aL aR cs kL (kR + 1)
    obtain ⟨s, f, w⟩ := c
    cases s
    · simp only [List.map_cons, sf, pointList, Bool.false_eq_true, if_false]
      simp only [origScore, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih2 ⊢
      rw [ih2, flip_term]
      simp only [flipSum, routeL, routeR, List.filter_cons, Bool.false_eq_true, if_false, Bool.not_false, if_true,
        List.map_cons, List.sum_cons, lfk]
      ring
    · simp only [List.map_cons, sf, pointList, if_true]
      simp only [origScore, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih1 ⊢
      rw [ih1, flip_term]
      simp only [flipSum, routeL, routeR, List.filter_cons, if_true, Bool.not_true, Bool.false_eq_true, if_false,
        List.map_cons, List.sum_cons, lfk]
      ring

/-- Zero padding to a width. -/
def padTo (w : ℕ) (L : List ℤ) : List ℤ := L ++ List.replicate (w - L.length) 0

theorem padTo_length (w : ℕ) (L : List ℤ) (h : L.length ≤ w) : (padTo w L).length = w := by
  simp [padTo]; omega

/-- The coordinate records of an exact gate under a side list and a flip list. -/
def coords {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) : List Coord :=
  List.ofFn fun i : Fin n => (side.getD i false, f.getD i false, e.weight i)

def pullDense {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) : ExactThresholdGate (width + width) :=
  ⟨fun j => (padTo width (routeL (coords side f e)) ++ padTo width (routeR (coords side f e))).getD j.val 0,
   e.target - flipSum (coords side f e)⟩

/-- The center assignment `(a_L, a_R)` as an input of the dense child. -/
def centerInput (width aL aR : ℕ) : BitInput (width + width) :=
  fun j => if j.val < width then aL.testBit j.val else aR.testBit (j.val - width)

/-- The pulled-back point of the original coordinates. -/
def pullPoint {n : ℕ} (side f : List Bool) (aL aR : ℕ) : BitInput n :=
  fun i => (pointList aL aR (List.ofFn fun j : Fin n => (side.getD j false, f.getD j false)) 0 0).getD i false

/-! ## The dense child holds exactly where the original child holds -/

theorem lfk_eq_sum (a : ℕ) : ∀ (L : List ℤ) (k w : ℕ), L.length ≤ w →
    lfk k L a = ∑ j ∈ Finset.range w, if a.testBit (k + j) then L.getD j 0 else 0
  | [], k, w, _ => by simp [lfk]
  | v :: L, k, w, h => by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ']
    simp only [lfk, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    rw [lfk_eq_sum a L (k + 1) w' (by simp at h; omega), add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show k + (j + 1) = k + 1 + j by omega]

theorem padTo_getD (w : ℕ) (L : List ℤ) (j : ℕ) : (padTo w L).getD j 0 = L.getD j 0 := by
  unfold padTo
  by_cases h : j < L.length
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default L 0 (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

theorem sum_fin_eq_range (w : ℕ) (g : ℕ → ℤ) : ∑ j : Fin w, g j.val = ∑ j ∈ Finset.range w, g j :=
  Fin.sum_univ_eq_sum_range g w

/-- The dense child's score at a center assignment is the sum of the two center-coordinate linear forms. -/
theorem dense_score (w aL aR : ℕ) (L R : List ℤ) (hL : L.length ≤ w) (hR : R.length ≤ w) :
    ∑ j : Fin (w + w), (padTo w L ++ padTo w R).getD j.val 0 * (if centerInput w aL aR j then 1 else 0) =
      lfk 0 L aL + lfk 0 R aR := by
  rw [Fin.sum_univ_add]
  have hP : (padTo w L).length = w := padTo_length w L hL
  have e1 : ∀ j : Fin w, (padTo w L ++ padTo w R).getD (Fin.castAdd w j).val 0 *
      (if centerInput w aL aR (Fin.castAdd w j) then 1 else 0) = if aL.testBit (0 + j.val) then L.getD j.val 0 else 0 := by
    intro j
    simp only [Fin.val_castAdd, centerInput, j.isLt, if_true, Nat.zero_add]
    rw [List.getD_append _ _ _ _ (by omega), padTo_getD]
    split_ifs <;> simp
  have e2 : ∀ j : Fin w, (padTo w L ++ padTo w R).getD (Fin.natAdd w j).val 0 *
      (if centerInput w aL aR (Fin.natAdd w j) then 1 else 0) = if aR.testBit (0 + j.val) then R.getD j.val 0 else 0 := by
    intro j
    simp only [Fin.val_natAdd, centerInput, show ¬ (w + j.val < w) by omega, if_false, Nat.add_sub_cancel_left,
      Nat.zero_add]
    rw [List.getD_append_right _ _ _ _ (by omega), hP, Nat.add_sub_cancel_left, padTo_getD]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_congr rfl (fun j _ => e2 j),
    sum_fin_eq_range w (fun j => if aL.testBit (0 + j) then L.getD j 0 else 0),
    sum_fin_eq_range w (fun j => if aR.testBit (0 + j) then R.getD j 0 else 0),
    lfk_eq_sum aL L 0 w hL, lfk_eq_sum aR R 0 w hR]

theorem coords_sf {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) :
    (coords side f e).map sf = List.ofFn fun j : Fin n => (side.getD j false, f.getD j false) := by
  simp [coords, sf, List.map_ofFn, Function.comp_def]

theorem zip_ofFn' {α β : Type} {n : ℕ} (c : Fin n → α) (x : Fin n → β) :
    (List.ofFn c).zip (List.ofFn x) = List.ofFn fun i => (c i, x i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

/-- The original score at an input is `origScore` of the coordinate records against the input bits. -/
theorem score_eq_origScore {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) (x : BitInput n) :
    ∑ i, e.weight i * (if x i then 1 else 0) = origScore (coords side f e) (List.ofFn x) := by
  unfold origScore coords
  rw [zip_ofFn', List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp]
  split_ifs <;> simp

theorem ofFn_pullPoint {n : ℕ} (side f : List Bool) (aL aR : ℕ) :
    List.ofFn (pullPoint (n := n) side f aL aR) =
      pointList aL aR (List.ofFn fun j : Fin n => (side.getD j false, f.getD j false)) 0 0 := by
  apply List.ext_getElem
  · simp [pointList_length]
  · intro i h1 h2
    simp only [List.getElem_ofFn, pullPoint]
    rw [List.getD_eq_getElem _ _ h2]

theorem pullDense_eval {n : ℕ} (side f : List Bool) (width aL aR : ℕ) (e : ExactThresholdGate n)
    (hL : (routeL (coords side f e)).length ≤ width) (hR : (routeR (coords side f e)).length ≤ width) :
    (pullDense side f width e).eval (centerInput width aL aR) = e.eval (pullPoint side f aL aR) := by
  unfold ExactThresholdGate.eval
  apply decide_eq_decide.mpr
  rw [score_eq_origScore side f e, ofFn_pullPoint, ← coords_sf side f e, origScore_eq]
  change ∑ j : Fin (width + width), (padTo width (routeL (coords side f e)) ++
      padTo width (routeR (coords side f e))).getD j.val 0 * (if centerInput width aL aR j then 1 else 0) =
      e.target - flipSum (coords side f e) ↔ _
  rw [dense_score width aL aR _ _ hL hR]
  constructor <;> intro h <;> linarith

/-! ## Exactness of a pulled-back atom -/

theorem sum_ind_of_count_le_one {β : Type} (L : List β) (p : β → Bool) (h : (L.filter p).length ≤ 1) :
    (L.map fun b => if p b then (1 : ℤ) else 0).sum = if L.any p then 1 else 0 := by
  induction L with
  | nil => simp
  | cons b L ih =>
    by_cases hb : p b = true
    · have h0 : (L.filter p).length = 0 := by
        simp only [List.filter_cons, hb, if_true, List.length_cons] at h; omega
      have hany : L.any p = false := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
        simp only [List.any_eq_false]; intro x hx; simpa using h0 x hx
      simp only [List.map_cons, List.sum_cons, List.any_cons, hb, Bool.true_or, if_true]
      rw [ih (by omega), hany]; simp
    · have hb' : p b = false := by simpa using hb
      simp only [List.filter_cons, hb', Bool.false_eq_true, if_false] at h
      simp only [List.map_cons, List.sum_cons, List.any_cons, hb', Bool.false_or, Bool.false_eq_true, if_false,
        zero_add]
      exact ih h

variable (a : DecompositionAlgorithm)

theorem gate_exact {n : ℕ} (g : SupportedNormalizedGate n) (x : BitInput n) :
    (if g.gate.eval x then (1 : ℤ) else 0) = ((children a g).map fun e => if e.eval x then (1 : ℤ) else 0).sum := by
  have heq := (a.output (request g)).equivalent x
  have hdis := (a.output (request g)).disjoint x
  change (nonStrictAsStrict g.gate).strictEval x = (children a g).any (fun child => child.eval x) at heq
  rw [nonStrictAsStrict_eval] at heq
  rw [sum_ind_of_count_le_one (children a g) (fun e => e.eval x) hdis, heq]

theorem atom_exact {n : ℕ} (g : SupportedNormalizedGate n) (side f : List Bool) (width aL aR : ℕ)
    (hL : ((List.ofFn fun j : Fin n => side.getD j false).filter id).length ≤ width)
    (hR : ((List.ofFn fun j : Fin n => side.getD j false).filter (fun b => !b)).length ≤ width) :
    (if g.gate.eval (pullPoint side f aL aR) then (1 : ℤ) else 0) =
      ((children a g).map fun e =>
        if (pullDense side f width e).eval (centerInput width aL aR) then (1 : ℤ) else 0).sum := by
  rw [gate_exact a g]
  congr 1
  apply List.map_congr_left
  intro e _
  have hl : ∀ e : ExactThresholdGate n, (routeL (coords side f e)).length =
      ((List.ofFn fun j : Fin n => side.getD j false).filter id).length := by
    intro e
    have hm : (coords side f e).map (fun c => c.1) = List.ofFn fun j : Fin n => side.getD j false := by
      simp [coords, List.map_ofFn, Function.comp_def]
    simp only [routeL, List.length_map]
    rw [← hm, List.filter_map, List.length_map]
    rfl
  have hr : ∀ e : ExactThresholdGate n, (routeR (coords side f e)).length =
      ((List.ofFn fun j : Fin n => side.getD j false).filter (fun b => !b)).length := by
    intro e
    have hm : (coords side f e).map (fun c => c.1) = List.ofFn fun j : Fin n => side.getD j false := by
      simp [coords, List.map_ofFn, Function.comp_def]
    simp only [routeR, List.length_map]
    rw [← hm, List.filter_map, List.length_map]
    rfl
  rw [pullDense_eval side f width aL aR e (by rw [hl]; exact hL) (by rw [hr]; exact hR)]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool

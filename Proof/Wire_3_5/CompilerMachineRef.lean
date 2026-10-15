import Proof.Wire_3_5.Contracts
import Proof.Wire_3_5.Shared.GF
import Proof.Wire_3_5.CompilerExpression

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs

/-! ## Syntactic separated equations and stacking -/

/-- A syntactic separated equation `a(z_L) + b(z_R) = 0`: its two half-scores. -/
abbrev SynEq : Type := HalfScore × HalfScore

/-- The value `a(z_L) + b(z_R)` at a column. -/
def SynEq.value (e : SynEq) (zL zR : ℕ) : ℤ := e.1.eval zL + e.2.eval zR

/-- The trivial equation `0 = 0`. -/
def zeroSyn : SynEq := (⟨0, []⟩, ⟨0, []⟩)

/-- Sum of two half-scores. -/
def addH (a b : HalfScore) : HalfScore := ⟨a.const + b.const, a.terms ++ b.terms⟩

/-- A half-score times an integer. -/
def scaleH (H : ℤ) (a : HalfScore) : HalfScore := ⟨H * a.const, a.terms.map fun t => (H * t.1, t.2)⟩

theorem eval_addH (a b : HalfScore) (z : ℕ) : (addH a b).eval z = a.eval z + b.eval z := by
  simp only [addH, HalfScore.eval, List.map_append, List.sum_append]; ring

theorem eval_scaleH (H : ℤ) (a : HalfScore) (z : ℕ) : (scaleH H a).eval z = H * a.eval z := by
  simp only [scaleH, HalfScore.eval, List.map_map]
  rw [mul_add, ← List.sum_map_mul_left]
  congr 2
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  split_ifs <;> simp

def stackSyn (H : ℤ) : List SynEq → SynEq
  | [] => zeroSyn
  | e :: es => (addH e.1 (scaleH H (stackSyn H es).1), addH e.2 (scaleH H (stackSyn H es).2))

/-- The semantic equation of a syntactic one. -/
def toSep (e : SynEq) : SeparatedEquation ℕ ℕ := ⟨fun zl => e.1.eval zl, fun zr => e.2.eval zr⟩

theorem value_stackSyn (H : ℤ) (zL zR : ℕ) :
    ∀ es : List SynEq, (stackSyn H es).value zL zR = eqValue (stackEquations H (es.map toSep)) zL zR
  | [] => by simp [stackSyn, zeroSyn, SynEq.value, HalfScore.eval, stackEquations, eqValue]
  | e :: es => by
    rw [List.map_cons, stack_value, ← value_stackSyn H zL zR es]
    simp only [stackSyn, SynEq.value, eval_addH, eval_scaleH, eqValue, toSep]
    ring

/-- **Stacking a syntactic conjunction** (`alg:stack`): with every stacked value bounded by `V_b < H`, the stacked
equation holds exactly when all of them hold. -/
theorem stackSyn_holds_iff (H Vb : ℤ) (hH : Vb < H) (es : List SynEq) (zL zR : ℕ)
    (hV : ∀ e ∈ es, |e.value zL zR| ≤ Vb) :
    (stackSyn H es).value zL zR = 0 ↔ ∀ e ∈ es, e.value zL zR = 0 := by
  have h := stack_holds_iff H Vb hH (es.map toSep) zL zR (by
    intro E hE
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hE
    exact hV e he)
  rw [holds_iff] at h
  rw [value_stackSyn, h]
  constructor
  · intro hall e he
    have := hall (toSep e) (List.mem_map_of_mem he)
    rwa [holds_iff] at this
  · intro hall E hE
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hE
    rw [holds_iff]; exact hall e he

/-! ## Labels, masks, cancellation, and the lifted unions -/

/-- The labels of atom `a`'s children: `[offset, offset + #children)` in the flattened pool. -/
def labelsOf (pool : List (List SynEq)) (a : ℕ) : List ℕ :=
  List.range' ((pool.take a).map List.length).sum (pool.getD a []).length

def monoMasks (pool : List (List SynEq)) : List ℕ → List ℕ
  | [] => [0]
  | a :: as => (labelsOf pool a).flatMap fun c => (monoMasks pool as).map fun u => 2 ^ c ||| u

/-- Remove equal adjacent pairs: on a sorted list, one copy of every value of odd multiplicity. -/
def cancelSorted : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: l => if x = y then cancelSorted l else x :: cancelSorted (y :: l)

def oddMasks (pool : List (List SynEq)) (p : F2Poly ℕ) : List ℕ :=
  cancelSorted ((p.flatMap (monoMasks pool)).mergeSort (fun a b => decide (a ≤ b)))

/-- The unions of the `ℓ`-subsets of a list of masks, in lexicographic order (`alg:binlift`'s `Σ_{|J|=ℓ}`). -/
def combosFrom : List ℕ → ℕ → List ℕ
  | _, 0 => [0]
  | [], _ + 1 => []
  | g :: G, ℓ + 1 => (combosFrom G ℓ).map (g ||| ·) ++ combosFrom G (ℓ + 1)

/-- The equations of the labels in a mask, in increasing label order. -/
def eqsOfMask (pool : List (List SynEq)) (U : ℕ) : List SynEq :=
  (pool.flatten.zipIdx.filter fun ec => U.testBit ec.2).map Prod.fst

/-- The stacked equation of a conjunction of labels. -/
def conjSyn (pool : List (List SynEq)) (H : ℤ) (U : ℕ) : SynEq := stackSyn H (eqsOfMask pool U)

def liftSyn (pool : List (List SynEq)) (H : ℤ) (Q : ℕ) (w : ℤ) (G : List ℕ) : List Occurrence :=
  (List.range Q).flatMap fun j => (combosFrom G (j + 1)).map fun U =>
    ⟨w * (-2) ^ j, (conjSyn pool H U).1, (conjSyn pool H U).2⟩

def compileRef (pool : List (List SynEq)) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) : List Occurrence :=
  (polarize m V).flatMap fun w => liftSyn pool H Q w.1 (oddMasks pool w.2)

/-! ## Meaning at one column -/

/-- The printer's table of an occurrence list at one column (the body of the seed's `PrinterReq.table`). -/
def occTable (out : List Occurrence) (zL zR : ℕ) : ℤ :=
  (out.map fun o => if o.left.eval zL + o.right.eval zR = 0 then o.v else 0).sum

/-- The atoms carry their exact children at the column: each atom's bit is the number of its children that hold. -/
def PoolExact (pool : List (List SynEq)) (zL zR : ℕ) (ρ : ℕ → Bool) : Prop :=
  ∀ a, bitZ (ρ a) = ((pool.getD a []).map fun e => bitZ (decide (e.value zL zR = 0))).sum

/-- The truth of a label at the column. -/
def lab (pool : List (List SynEq)) (zL zR : ℕ) (c : ℕ) : Bool := decide ((pool.flatten.getD c zeroSyn).value zL zR = 0)

/-- A mask holds: every label it contains (below the pool size) holds. -/
def maskHolds (pool : List (List SynEq)) (zL zR : ℕ) (U : ℕ) : Bool :=
  decide (∀ c < pool.flatten.length, U.testBit c = true → lab pool zL zR c = true)

theorem maskHolds_zero (pool : List (List SynEq)) (zL zR : ℕ) : maskHolds pool zL zR 0 = true := by
  simp [maskHolds]

theorem maskHolds_or (pool : List (List SynEq)) (zL zR : ℕ) (g u : ℕ) :
    maskHolds pool zL zR (g ||| u) = (maskHolds pool zL zR g && maskHolds pool zL zR u) := by
  simp only [maskHolds, Nat.testBit_or, Bool.or_eq_true]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h; exact ⟨fun c hc hg => h c hc (Or.inl hg), fun c hc hu => h c hc (Or.inr hu)⟩
  · rintro ⟨h1, h2⟩ c hc (hg | hu)
    · exact h1 c hc hg
    · exact h2 c hc hu

theorem maskHolds_single (pool : List (List SynEq)) (zL zR : ℕ) (c u : ℕ) (hc : c < pool.flatten.length) :
    maskHolds pool zL zR (2 ^ c ||| u) = (lab pool zL zR c && maskHolds pool zL zR u) := by
  rw [maskHolds_or]
  congr 1
  simp only [maskHolds, Nat.testBit_two_pow, decide_eq_true_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact h c hc rfl
  · intro h c' _ hc'; subst hc'; exact h

/-- **The union count** (`alg:binlift`'s `Σ_{|J|=ℓ} ∏_{j∈J} G_j = C(#true, ℓ)`). -/
theorem sum_combosFrom (f : ℕ → Bool) (hf0 : f 0 = true) (hor : ∀ g u, f (g ||| u) = (f g && f u)) :
    ∀ (G : List ℕ) (ℓ : ℕ), ((combosFrom G ℓ).map fun U => bitZ (f U)).sum = ((G.filter f).length.choose ℓ : ℤ)
  | G, 0 => by cases G <;> simp [combosFrom, hf0, bitZ]
  | [], ℓ + 1 => by simp [combosFrom]
  | g :: G, ℓ + 1 => by
    rw [combosFrom, List.map_append, List.sum_append, List.map_map, sum_combosFrom f hf0 hor G (ℓ + 1)]
    have : ((combosFrom G ℓ).map ((fun U => bitZ (f U)) ∘ (g ||| ·))) =
        (combosFrom G ℓ).map fun U => bitZ (f g) * bitZ (f U) := by
      apply List.map_congr_left
      intro U _
      simp only [Function.comp, hor]
      cases f g <;> cases f U <;> simp [bitZ]
    rw [this, List.sum_map_mul_left, sum_combosFrom f hf0 hor G ℓ]
    by_cases hg : f g = true
    · simp only [List.filter_cons, hg, if_true, List.length_cons, Nat.choose_succ_succ', bitZ]
      push_cast; ring
    · simp only [List.filter_cons, hg, Bool.false_eq_true, if_false, bitZ]
      simp

theorem length_combosFrom : ∀ (G : List ℕ) (ℓ : ℕ), (combosFrom G ℓ).length = G.length.choose ℓ
  | G, 0 => by cases G <;> simp [combosFrom]
  | [], ℓ + 1 => by simp [combosFrom]
  | g :: G, ℓ + 1 => by
    rw [combosFrom, List.length_append, List.length_map, length_combosFrom G ℓ, length_combosFrom G (ℓ + 1)]
    simp [Nat.choose_succ_succ']

theorem sum_neg_two_choose (Q t : ℕ) :
    ∑ j ∈ Finset.range Q, (-2 : ℤ) ^ j * ((t.choose (j + 1) : ℕ) : ℤ) = ThresholdCompiler.binLift Q t := by
  unfold ThresholdCompiler.binLift
  rcases le_total Q t with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    have hsplit := Finset.sum_range_add (fun j => (-2 : ℤ) ^ j * ((t.choose (j + 1) : ℕ) : ℤ)) t (Q - t)
    rw [Nat.add_sub_cancel' h] at hsplit
    rw [hsplit]
    have : ∑ x ∈ Finset.range (Q - t), (-2 : ℤ) ^ (t + x) * ((t.choose (t + x + 1) : ℕ) : ℤ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [this, add_zero]

/-! ## The cancelled substitution has the parity of the polynomial -/

theorem cancelSorted_count_mod (f : ℕ → Bool) :
    ∀ l : List ℕ, (cancelSorted l).countP f % 2 = l.countP f % 2
  | [] => rfl
  | [x] => rfl
  | x :: y :: l => by
    unfold cancelSorted
    split_ifs with hxy
    · subst hxy
      have ih := cancelSorted_count_mod f l
      rw [List.countP_cons, List.countP_cons]
      by_cases h : f x = true
      · simp only [h, if_true]; omega
      · simp only [h]; omega
    · have ih := cancelSorted_count_mod f (y :: l)
      rw [List.countP_cons, List.countP_cons (a := x) (l := y :: l)]
      by_cases h : f x = true
      · simp only [h, if_true]; omega
      · simp only [h]; omega
termination_by l => l.length

theorem labelsOf_lt (pool : List (List SynEq)) (a c : ℕ) (hc : c ∈ labelsOf pool a) : c < pool.flatten.length := by
  unfold labelsOf at hc
  rw [List.mem_range'_1] at hc
  have key : ∀ (L : List (List SynEq)) (i : ℕ), ((L.take i).map List.length).sum + (L.getD i []).length ≤
      L.flatten.length := by
    intro L
    induction L with
    | nil => intro i; simp
    | cons A L ih =>
      intro i
      cases i with
      | zero => simp
      | succ i =>
        have := ih i
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ, List.flatten_cons,
          List.length_append]
        omega
  have := key pool a
  omega

theorem getD_flatten_offset' (L : List (List SynEq)) (i j : ℕ) (hj : j < (L.getD i []).length) :
    L.flatten.getD (((L.take i).map List.length).sum + j) zeroSyn = (L.getD i []).getD j zeroSyn := by
  induction L generalizing i with
  | nil => simp at hj
  | cons A L ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add, List.flatten_cons]
      simp only [List.getD_cons_zero] at hj ⊢
      rw [List.getD_append _ _ _ _ hj]
    | succ i =>
      simp only [List.getD_cons_succ] at hj ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
      rw [Nat.add_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact ih i hj

theorem length_filter_eq_sum (l : List ℕ) (f : ℕ → Bool) :
    (((l.filter f).length : ℕ) : ℤ) = (l.map fun c => bitZ (f c)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : f a = true
    · simp [h, ih, bitZ]; ring
    · simp [h, ih, bitZ]

theorem sum_map_eq_range_getD {β : Type} (l : List β) (d : β) (g : β → ℤ) :
    (l.map g).sum = ((List.range l.length).map fun j => g (l.getD j d)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.getD_cons_zero]
    rw [ih]
    congr 1

/-- The number of an atom's children that hold is its bit (exactness). -/
theorem count_labels (pool : List (List SynEq)) (zL zR : ℕ) (ρ : ℕ → Bool) (hex : PoolExact pool zL zR ρ) (a : ℕ) :
    (((labelsOf pool a).filter (lab pool zL zR)).length : ℤ) = bitZ (ρ a) := by
  rw [length_filter_eq_sum, hex a, sum_map_eq_range_getD (pool.getD a []) zeroSyn]
  unfold labelsOf
  rw [List.range'_eq_map_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp, lab]
  rw [getD_flatten_offset' pool a j (List.mem_range.mp hj)]

theorem sum_ite_const (l : List ℕ) (f : ℕ → Bool) (K : ℕ) :
    (l.map fun c => if f c = true then K else 0).sum = l.countP f * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : f a = true
    · simp [h]; ring
    · simp [h]

/-- The holding masks of one monomial: the product over its atoms of the numbers of holding children. -/
theorem countP_monoMasks (pool : List (List SynEq)) (zL zR : ℕ) :
    ∀ mono : List ℕ, (monoMasks pool mono).countP (maskHolds pool zL zR) =
      (mono.map fun a => (labelsOf pool a).countP (lab pool zL zR)).prod
  | [] => by simp [monoMasks, maskHolds_zero]
  | a :: as => by
    rw [monoMasks, List.countP_flatMap, List.map_cons, List.prod_cons, ← countP_monoMasks pool zL zR as]
    have hterm : ∀ c ∈ labelsOf pool a, ((monoMasks pool as).map (2 ^ c ||| ·)).countP (maskHolds pool zL zR) =
        if lab pool zL zR c = true then (monoMasks pool as).countP (maskHolds pool zL zR) else 0 := by
      intro c hc
      have hlt := labelsOf_lt pool a c hc
      rw [List.countP_map]
      split_ifs with h
      · congr 1; funext u; simp only [Function.comp, maskHolds_single _ _ _ c u hlt, h, Bool.true_and]
      · rw [List.countP_eq_zero]
        intro u _
        simp only [Function.comp, maskHolds_single _ _ _ c u hlt, Bool.and_eq_true, not_and]
        intro h'; exact absurd h' h
    have hmap : (labelsOf pool a).map (List.countP (maskHolds pool zL zR) ∘
        fun c => (monoMasks pool as).map fun u => 2 ^ c ||| u) =
        (labelsOf pool a).map fun c => if lab pool zL zR c = true then
          (monoMasks pool as).countP (maskHolds pool zL zR) else 0 :=
      List.map_congr_left fun c hc => by simp only [Function.comp]; exact hterm c hc
    rw [hmap, sum_ite_const]

/-- With exact children, a monomial's number of holding masks is `1` if all its atoms hold and `0` otherwise. -/
theorem countP_monoMasks_exact (pool : List (List SynEq)) (zL zR : ℕ) (ρ : ℕ → Bool) (hex : PoolExact pool zL zR ρ)
    (mono : List ℕ) : (monoMasks pool mono).countP (maskHolds pool zL zR) = if mono.all ρ then 1 else 0 := by
  rw [countP_monoMasks]
  have ha : ∀ a, (labelsOf pool a).countP (lab pool zL zR) = if ρ a then 1 else 0 := by
    intro a
    have h := count_labels pool zL zR ρ hex a
    rw [← List.countP_eq_length_filter] at h
    cases hρ : ρ a <;> rw [hρ] at h <;> simp only [bitZ, Bool.false_eq_true, if_false, if_true] at h ⊢ <;>
      exact_mod_cast h
  induction mono with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons, ih, ha, List.all_cons]
    cases ρ a <;> cases as.all ρ <;> simp

theorem bitZ_xorAll_countP : ∀ bs : List Bool, bitZ (xorAll bs) = ((bs.countP id : ℕ) : ℤ) % 2
  | [] => by simp [xorAll, bitZ]
  | b :: bs => by
    rw [xorAll, bitZ_xor, bitZ_xorAll_countP bs, List.countP_cons]
    cases b
    · simp [bitZ]
    · simp only [bitZ, id, if_true]
      push_cast
      omega

theorem countP_flatMap_monoMasks (pool : List (List SynEq)) (zL zR : ℕ) (ρ : ℕ → Bool)
    (hex : PoolExact pool zL zR ρ) :
    ∀ p : F2Poly ℕ, (p.flatMap (monoMasks pool)).countP (maskHolds pool zL zR) = (p.map fun m => m.all ρ).countP id
  | [] => by simp
  | mono :: p => by
    rw [List.flatMap_cons, List.countP_append, countP_flatMap_monoMasks pool zL zR ρ hex p,
      countP_monoMasks_exact pool zL zR ρ hex mono, List.map_cons, List.countP_cons]
    cases mono.all ρ <;> simp [add_comm]

theorem oddMasks_parity (pool : List (List SynEq)) (zL zR : ℕ) (ρ : ℕ → Bool) (hex : PoolExact pool zL zR ρ)
    (p : F2Poly ℕ) :
    (((oddMasks pool p).countP (maskHolds pool zL zR) : ℕ) : ℤ) % 2 = bitZ (F2Poly.eval p ρ) := by
  have h1 : (oddMasks pool p).countP (maskHolds pool zL zR) % 2 =
      (p.map fun m => m.all ρ).countP id % 2 := by
    unfold oddMasks
    rw [cancelSorted_count_mod, (List.mergeSort_perm _ _).countP_eq, countP_flatMap_monoMasks pool zL zR ρ hex p]
  rw [F2Poly.eval_eq_xorAll, bitZ_xorAll_countP]
  have := congrArg (Nat.cast : ℕ → ℤ) h1
  push_cast at this
  exact this

/-- Membership in the equations of a mask. -/
theorem forall_eqsOfMask (pool : List (List SynEq)) (U : ℕ) (P : SynEq → Prop) :
    (∀ e ∈ eqsOfMask pool U, P e) ↔
      ∀ c < pool.flatten.length, U.testBit c = true → P (pool.flatten.getD c zeroSyn) := by
  unfold eqsOfMask
  simp only [List.mem_map, List.mem_filter, Prod.exists, exists_and_right, exists_eq_right, forall_exists_index,
    and_imp]
  constructor
  · intro h c hc hU
    apply h _ c _ hU
    rw [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem _ _ hc, List.getElem?_eq_getElem hc]
  · intro h e c hmem hU
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    have hc : c < pool.flatten.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hmem; simp at hmem
    have := h c hc hU
    rw [List.getD_eq_getElem _ _ hc] at this
    rw [List.getElem?_eq_getElem hc] at hmem
    simp only [Option.some.injEq] at hmem
    rwa [← hmem]

/-- **A stacked conjunction holds exactly when its mask holds** (children bounded by `V_b < H`). -/
theorem conjSyn_holds_iff (pool : List (List SynEq)) (H Vb : ℤ) (hH : Vb < H) (zL zR : ℕ)
    (hV : ∀ e ∈ pool.flatten, |e.value zL zR| ≤ Vb) (U : ℕ) :
    (conjSyn pool H U).value zL zR = 0 ↔ maskHolds pool zL zR U = true := by
  unfold conjSyn
  rw [stackSyn_holds_iff H Vb hH _ zL zR (fun e he => by
    apply hV e
    unfold eqsOfMask at he
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
    have hz := (List.mem_zipIdx_iff_getElem?).mp (List.mem_filter.mp hec).1
    exact List.mem_of_getElem? hz)]
  rw [forall_eqsOfMask]
  simp only [maskHolds, lab, decide_eq_true_eq]

theorem occTable_append (a b : List Occurrence) (zL zR : ℕ) :
    occTable (a ++ b) zL zR = occTable a zL zR + occTable b zL zR := by
  simp [occTable, List.map_append, List.sum_append]

theorem occTable_flatMap {β : Type} (L : List β) (f : β → List Occurrence) (zL zR : ℕ) :
    occTable (L.flatMap f) zL zR = (L.map fun b => occTable (f b) zL zR).sum := by
  induction L with
  | nil => simp [occTable]
  | cons b L ih => rw [List.flatMap_cons, occTable_append, ih, List.map_cons, List.sum_cons]

theorem list_range_sum (f : ℕ → ℤ) : ∀ Q, ((List.range Q).map f).sum = ∑ j ∈ Finset.range Q, f j
  | 0 => by simp
  | Q + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_range_sum f Q, Finset.sum_range_succ]; simp

/-- One lifted polynomial's table: `w·BinLift_{Q'}(t)` with `t` the number of holding masks. -/
theorem occTable_liftSyn (pool : List (List SynEq)) (H Vb : ℤ) (hH : Vb < H) (zL zR : ℕ)
    (hV : ∀ e ∈ pool.flatten, |e.value zL zR| ≤ Vb) (Q : ℕ) (w : ℤ) (G : List ℕ) :
    occTable (liftSyn pool H Q w G) zL zR =
      w * ThresholdCompiler.binLift Q ((G.filter (maskHolds pool zL zR)).length) := by
  unfold liftSyn
  rw [occTable_flatMap, ← sum_neg_two_choose, Finset.mul_sum, list_range_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold occTable
  rw [List.map_map]
  have hterm : ∀ U ∈ combosFrom G (j + 1),
      ((fun o : Occurrence => if o.left.eval zL + o.right.eval zR = 0 then o.v else 0) ∘
        fun U => (⟨w * (-2) ^ j, (conjSyn pool H U).1, (conjSyn pool H U).2⟩ : Occurrence)) U =
      w * (-2) ^ j * bitZ (maskHolds pool zL zR U) := by
    intro U _
    simp only [Function.comp]
    have hiff := conjSyn_holds_iff pool H Vb hH zL zR hV U
    unfold SynEq.value at hiff
    by_cases hm : maskHolds pool zL zR U = true
    · rw [if_pos (hiff.mpr hm), hm]; simp [bitZ]
    · rw [if_neg (fun h => hm (hiff.mp h))]
      simp only [Bool.not_eq_true] at hm
      simp [hm, bitZ]
  rw [List.map_congr_left hterm, List.sum_map_mul_left,
    sum_combosFrom _ (maskHolds_zero pool zL zR) (maskHolds_or pool zL zR) G (j + 1)]
  ring

theorem compileRef_modEq (pool : List (List SynEq)) (H Vb : ℤ) (hH : Vb < H) (m Q : ℕ) (hm : 1 ≤ m)
    (V : IntExpression ℕ) (hVm : ∀ t ∈ V, t.2.length ≤ m) (zL zR : ℕ)
    (hV : ∀ e ∈ pool.flatten, |e.value zL zR| ≤ Vb) (ρ : ℕ → Bool) (hex : PoolExact pool zL zR ρ) :
    occTable (compileRef pool H m Q V) zL zR ≡ 2 ^ (m - 1) * IntExpression.eval V ρ [ZMOD (2 : ℤ) ^ Q] := by
  unfold compileRef
  rw [occTable_flatMap, ← polarize_value m hm V hVm ρ]
  unfold signedValue
  apply modEq_list_sum
  intro w _
  rw [occTable_liftSyn pool H Vb hH zL zR hV]
  apply Int.ModEq.mul_left
  refine (ThresholdCompiler.binLiftModEqParity Q _).trans ?_
  have hp := oddMasks_parity pool zL zR ρ hex w.2
  have heq : ((((oddMasks pool w.2).filter (maskHolds pool zL zR)).length % 2 : ℕ) : ℤ) =
      bitZ (F2Poly.eval w.2 ρ) := by
    rw [← hp, ← List.countP_eq_length_filter]
    push_cast
    rfl
  rw [heq]

/-! ## The occurrence bound -/

theorem cancelSorted_sublist : ∀ l : List ℕ, List.Sublist (cancelSorted l) l
  | [] => List.Sublist.slnil
  | [x] => List.Sublist.refl _
  | x :: y :: l => by
    unfold cancelSorted
    split_ifs
    · exact ((cancelSorted_sublist l).cons y).cons x
    · exact (cancelSorted_sublist (y :: l)).cons_cons x
termination_by l => l.length

theorem cancelSorted_sorted : ∀ l : List ℕ, l.Pairwise (· ≤ ·) → (cancelSorted l).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [x], _ => List.pairwise_singleton _ _
  | x :: y :: l, h => by
    unfold cancelSorted
    split_ifs with hxy
    · exact cancelSorted_sorted l (List.Pairwise.of_cons (List.Pairwise.of_cons h))
    · have hyl := List.Pairwise.of_cons h
      have ih := cancelSorted_sorted (y :: l) hyl
      refine List.Pairwise.cons ?_ ih
      intro b hb
      have hb' := (cancelSorted_sublist (y :: l)).subset hb
      have hxb : x ≤ b := (List.pairwise_cons.mp h).1 b hb'
      have hxy' : x ≤ y := (List.pairwise_cons.mp h).1 y List.mem_cons_self
      rcases List.mem_cons.mp hb' with rfl | hbl
      · omega
      · have hyb : b ≥ y := (List.pairwise_cons.mp hyl).1 b hbl
        omega
termination_by l => l.length

theorem oddMasks_nodup (pool : List (List SynEq)) (p : F2Poly ℕ) : (oddMasks pool p).Nodup := by
  unfold oddMasks
  have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (p.flatMap (monoMasks pool))
  have hs' : ((p.flatMap (monoMasks pool)).mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) :=
    hs.imp fun h => by simpa using h
  exact (cancelSorted_sorted _ hs').imp fun h => ne_of_lt h

theorem monoMasks_mem (pool : List (List SynEq)) :
    ∀ (mono : List ℕ) (u : ℕ), u ∈ monoMasks pool mono →
      ∃ S : Finset ℕ, S ⊆ Finset.range pool.flatten.length ∧ S.card ≤ mono.length ∧
        u = Finset.equivBitIndices.symm S
  | [], u, hu => by
    simp only [monoMasks, List.mem_singleton] at hu
    exact ⟨∅, Finset.empty_subset _, by simp, by rw [hu]; rfl⟩
  | a :: as, u, hu => by
    simp only [monoMasks, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨c, hc, u', hu', rfl⟩ := hu
    obtain ⟨S, hS, hcard, rfl⟩ := monoMasks_mem pool as u' hu'
    have hlt := labelsOf_lt pool a c hc
    refine ⟨insert c S, Finset.insert_subset (Finset.mem_range.mpr hlt) hS,
      (Finset.card_insert_le c S).trans (by simp; omega), ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_two_pow, GF.testBit_equivBitIndices_symm, GF.testBit_equivBitIndices_symm]
    by_cases hi : i = c
    · subst hi; simp
    · have : c ≠ i := fun h => hi h.symm
      simp [this, hi]

theorem oddMasks_length_le (pool : List (List SynEq)) (d : ℕ) (p : F2Poly ℕ) (hd : ∀ mono ∈ p, mono.length ≤ d) :
    (oddMasks pool p).length ≤ (pool.flatten.length + 1) ^ d := by
  classical
  set T := ((Finset.range pool.flatten.length).powerset.filter fun S => S.card ≤ d).image Finset.equivBitIndices.symm
  have hsub : (oddMasks pool p).toFinset ⊆ T := by
    intro u hu
    rw [List.mem_toFinset] at hu
    unfold oddMasks at hu
    have hu1 := (cancelSorted_sublist _).subset hu
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_flatMap] at hu1
    obtain ⟨mono, hmono, hu2⟩ := hu1
    obtain ⟨S, hS, hcard, rfl⟩ := monoMasks_mem pool mono u hu2
    exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hcard.trans (hd mono hmono)⟩,
      rfl⟩
  calc (oddMasks pool p).length = (oddMasks pool p).toFinset.card :=
        (List.toFinset_card_of_nodup (oddMasks_nodup pool p)).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ ((Finset.range pool.flatten.length).powerset.filter fun S => S.card ≤ d).card := Finset.card_image_le
    _ ≤ ((Finset.range pool.flatten.length).card + 1) ^ d := card_powerset_filter_le _ d
    _ = (pool.flatten.length + 1) ^ d := by rw [Finset.card_range]

theorem length_liftSyn (pool : List (List SynEq)) (H : ℤ) (Q : ℕ) (w : ℤ) (G : List ℕ) :
    (liftSyn pool H Q w G).length = ∑ j ∈ Finset.range Q, G.length.choose (j + 1) := by
  unfold liftSyn
  rw [List.length_flatMap]
  simp only [List.length_map, length_combosFrom]
  induction Q with
  | zero => simp
  | succ Q ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem compileRef_length_le (pool : List (List SynEq)) (H : ℤ) (m Q d : ℕ) (V : IntExpression ℕ)
    (hVm : ∀ t ∈ V, t.2.length ≤ m) (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) :
    (compileRef pool H m Q V).length ≤ V.length * 2 ^ m * (Q * (pool.flatten.length + 1) ^ (Q * d)) := by
  unfold compileRef
  rw [List.length_flatMap]
  have hterm : ∀ w ∈ polarize m V, (liftSyn pool H Q w.1 (oddMasks pool w.2)).length ≤
      Q * (pool.flatten.length + 1) ^ (Q * d) := by
    intro w hw
    rw [length_liftSyn]
    have hG := oddMasks_length_le pool d w.2 (by
      intro mono hmono
      rcases polarize_mono_mem m V w hw mono hmono with h | ⟨t, ht, p, hp, hm⟩
      · subst h; simp
      · exact hd t ht p hp mono hm)
    calc ∑ j ∈ Finset.range Q, (oddMasks pool w.2).length.choose (j + 1)
        ≤ Q * max 1 (oddMasks pool w.2).length ^ Q := binLift_count_le Q _
      _ ≤ Q * ((pool.flatten.length + 1) ^ d) ^ Q := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_left
          exact max_le (Nat.one_le_pow _ _ (by omega)) hG
      _ = Q * (pool.flatten.length + 1) ^ (Q * d) := by rw [← pow_mul, mul_comm d Q]
  calc ((polarize m V).map fun w => (liftSyn pool H Q w.1 (oddMasks pool w.2)).length).sum
      ≤ ((polarize m V).map fun _ => Q * (pool.flatten.length + 1) ^ (Q * d)).sum := by
        apply List.sum_le_sum; intro w hw; exact hterm w hw
    _ = (polarize m V).length * (Q * (pool.flatten.length + 1) ^ (Q * d)) := by simp
    _ ≤ V.length * 2 ^ m * (Q * (pool.flatten.length + 1) ^ (Q * d)) :=
        Nat.mul_le_mul_right _ (polarize_length_le m V hVm)

end NearCubicWires.WireExponent3_5.CompilerMachine

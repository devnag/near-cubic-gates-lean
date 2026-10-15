import Proof.Wire_3_5.CompilerMachineReqContract

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut cutWord signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-! ## The records of one label -/

theorem pairs_length {β : Type} (A B : ℕ → β) (N : ℕ) :
    ((List.range N).flatMap fun q => [A q, B q]).length = 2 * N := by
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  ring

theorem pairs_getD {β : Type} (A B : ℕ → β) (d : β) : ∀ N q, q < N →
    ((List.range N).flatMap fun q => [A q, B q]).getD (2 * q) d = A q ∧
      ((List.range N).flatMap fun q => [A q, B q]).getD (2 * q + 1) d = B q
  | 0, q, h => absurd h (Nat.not_lt_zero q)
  | N + 1, q, h => by
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · obtain ⟨h1, h2⟩ := pairs_getD A B d N q h'
      have hl := pairs_length A B N
      refine ⟨?_, ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h2
    · have hl := pairs_length A B q
      refine ⟨?_, ?_⟩
      · rw [List.getD_append_right _ _ _ _ (by omega), hl]; simp
      · rw [List.getD_append_right _ _ _ _ (by omega), hl]; simp

/-- The records of a pool child: C3a's dense records. -/
def labRecs (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (fe : List Bool × ExactThresholdGate n) :
    List (List Bool) :=
  denseRecs h side fe.1 width fe.2

theorem denseRecs_getD (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) (q : ℕ)
    (hq : q < width + width + 1) :
    (denseRecs h side f width e).getD (2 * q) [] = binary h (fieldPN side f width e q).1 ∧
      (denseRecs h side f width e).getD (2 * q + 1) [] = binary h (fieldPN side f width e q).2 :=
  pairs_getD (fun q => binary h (fieldPN side f width e q).1) (fun q => binary h (fieldPN side f width e q).2) [] _ q hq

/-- **The stack records** of a list of pool children: record `r` is the sentinel `true` followed by the `r`-th words
of the children, concatenated in order. -/
def stackRecs (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n)) :
    List (List Bool) :=
  (List.range (2 * (width + width + 1))).map fun r => true :: L.flatMap fun fe => (labRecs h side width fe).getD r []

theorem stackRecs_nil (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) :
    stackRecs h side width ([] : List (List Bool × ExactThresholdGate n)) =
      List.replicate (2 * (width + width + 1)) [true] := by
  simp [stackRecs, List.map_const']

theorem stackRecs_snoc (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n))
    (fe : List Bool × ExactThresholdGate n) :
    stackRecs h side width (L ++ [fe]) = (List.range (2 * (width + width + 1))).map fun r =>
      (stackRecs h side width L).getD r [] ++ (labRecs h side width fe).getD r [] := by
  unfold stackRecs
  apply List.map_congr_left
  intro r hr
  rw [List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp hr), List.getElem_map, List.getElem_range]
  simp

/-! ## The fields of a stacked equation -/

/-- Field `q` of an equation over the two center halves: left weights, right weights, then the target. -/
def fieldOf {w : ℕ} (E : RowBinLift.Equation w w) (q : ℕ) : ℤ :=
  if h : q < w then E.weights (Sum.inl ⟨q, h⟩)
  else if h' : q < w + w then E.weights (Sum.inr ⟨q - w, by omega⟩) else E.target

theorem fieldOf_cons {w : ℕ} (H : ℤ) (e : RowBinLift.Equation w w) (es : List (RowBinLift.Equation w w)) (q : ℕ) :
    fieldOf (SupplierPipeline.stackEquations H (e :: es)) q =
      fieldOf e q + H * fieldOf (SupplierPipeline.stackEquations H es) q := by
  unfold fieldOf
  split_ifs <;> rfl

theorem fieldOf_nil {w : ℕ} (H : ℤ) (q : ℕ) :
    fieldOf (SupplierPipeline.stackEquations H ([] : List (RowBinLift.Equation w w))) q = 0 := by
  unfold fieldOf
  split_ifs <;> rfl

theorem fieldOf_eqOf {w : ℕ} (e : ExactThresholdGate (w + w)) (q : ℕ) :
    fieldOf (eqOf e) q = if h : q < w + w then e.weight ⟨q, h⟩ else e.target := by
  unfold fieldOf eqOf
  by_cases h1 : q < w
  · rw [dif_pos h1, dif_pos (by omega)]
    rfl
  · by_cases h2 : q < w + w
    · rw [dif_neg h1, dif_pos h2, dif_pos h2]
      show e.weight (Fin.natAdd w ⟨q - w, _⟩) = _
      congr 1
      ext
      simp only [Fin.val_natAdd]
      omega
    · rw [dif_neg h1, dif_neg h2, dif_neg h2]

theorem stackRecs_P (h : ℕ) {n : ℕ} (side : List Bool) (width q : ℕ) (hq : q < width + width + 1)
    (M : List (List Bool × ExactThresholdGate n)) :
    ((stackRecs h side width M).getD (2 * q) []).tail = M.flatMap fun x => binary h (fieldPN side x.1 width x.2 q).1 := by
  have h1 : 2 * q < (List.range (2 * (width + width + 1))).length := by simp; omega
  simp only [stackRecs]
  rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_map, List.getElem_range, List.tail_cons]
  apply List.flatMap_congr
  intro x _
  exact (denseRecs_getD h side x.1 width x.2 q hq).1

theorem stackRecs_N (h : ℕ) {n : ℕ} (side : List Bool) (width q : ℕ) (hq : q < width + width + 1)
    (M : List (List Bool × ExactThresholdGate n)) :
    ((stackRecs h side width M).getD (2 * q + 1) []).tail =
      M.flatMap fun x => binary h (fieldPN side x.1 width x.2 q).2 := by
  have h1 : 2 * q + 1 < (List.range (2 * (width + width + 1))).length := by simp; omega
  simp only [stackRecs]
  rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_map, List.getElem_range, List.tail_cons]
  apply List.flatMap_congr
  intro x _
  exact (denseRecs_getD h side x.1 width x.2 q hq).2

theorem value_pn (h : ℕ) {n : ℕ} (side : List Bool) (width q : ℕ) :
    ∀ L : List (List Bool × ExactThresholdGate n),
      (∀ fe ∈ L, (fieldPN side fe.1 width fe.2 q).1 < 2 ^ h ∧ (fieldPN side fe.1 width fe.2 q).2 < 2 ^ h) →
      (value (L.flatMap fun x => binary h (fieldPN side x.1 width x.2 q).1) : ℤ) -
          value (L.flatMap fun x => binary h (fieldPN side x.1 width x.2 q).2) =
        fieldOf (SupplierPipeline.stackEquations (2 ^ h) (L.map fun fe => eqOf (pullDense side fe.1 width fe.2))) q
  | [], _ => by simp [value, fieldOf_nil]
  | fe :: L, hL => by
    have ih := value_pn h side width q L (fun x hx => hL x (List.mem_cons_of_mem fe hx))
    obtain ⟨hP, hN⟩ := hL fe List.mem_cons_self
    have hv := fieldPN_value side fe.1 width fe.2 q
    rw [List.flatMap_cons, List.flatMap_cons, RadixSemantics.value_append, RadixSemantics.value_append, binary_length,
      binary_length, binary_value h _ hP, binary_value h _ hN, List.map_cons, fieldOf_cons, ← ih, fieldOf_eqOf, ← hv]
    push_cast
    ring

/-- **The P/N stack is the stacked field** (alg:stack with `H = 2^h`): for every field `q ≤ 2w`, the
concatenated P words minus the concatenated N words is field `q` of base's `stackEquations (2^h)` of the dense
children. -/
theorem stack_value (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (q : ℕ) (hq : q < width + width + 1)
    (L : List (List Bool × ExactThresholdGate n))
    (hL : ∀ fe ∈ L, (fieldPN side fe.1 width fe.2 q).1 < 2 ^ h ∧ (fieldPN side fe.1 width fe.2 q).2 < 2 ^ h) :
    (value (((stackRecs h side width L).getD (2 * q) []).tail) : ℤ) -
        value (((stackRecs h side width L).getD (2 * q + 1) []).tail) =
      fieldOf (SupplierPipeline.stackEquations (2 ^ h) (L.map fun fe => eqOf (pullDense side fe.1 width fe.2))) q := by
  rw [stackRecs_P h side width q hq, stackRecs_N h side width q hq]
  exact value_pn h side width q L hL

/-! ## The labels of a mask -/

/-- The children of the labels of `U` among the first `j` labels, in label order. -/
def selAt {α : Type} (PC : List α) (U j : ℕ) : List α :=
  (((PC.take j).zipIdx).filter fun ec => U.testBit ec.2).map Prod.fst

theorem selAt_zero {α : Type} (PC : List α) (U : ℕ) : selAt PC U 0 = [] := by simp [selAt]

theorem selAt_succ {α : Type} (PC : List α) (U j : ℕ) (hj : j < PC.length) :
    selAt PC U (j + 1) = selAt PC U j ++ (if U.testBit j then [PC[j]] else []) := by
  unfold selAt
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.zipIdx_append, List.filter_append,
    List.map_append]
  congr 1
  have hlen : (PC.take j).length = j := by simp; omega
  rw [hlen]
  by_cases hb : U.testBit j <;> simp [hb]

/-- **The children of a mask's labels are C3a's dense pool children**, in label order. -/
theorem denseLabels_eq {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) (U : ℕ) (a : DecompositionAlgorithm) :
    denseLabels (densePool a gates side width flips) U =
      (selAt (poolChildren a gates flips) U (poolChildren a gates flips).length).map
        fun fe => pullDense side fe.1 width fe.2 := by
  have hf : ∀ fl : List (List Bool), (densePool a gates side width fl).flatten =
      (poolChildren a gates fl).map fun fe => pullDense side fe.1 width fe.2 := by
    intro fl
    induction fl with
    | nil => rfl
    | cons f fs ih =>
      unfold densePool poolChildren at *
      rw [List.flatMap_cons, List.flatMap_cons, List.flatten_append, List.map_append, ih]
      congr 1
      rw [← List.flatMap_def, List.map_flatMap]
      apply List.flatMap_congr
      intro g _
      rw [List.map_map]
      rfl
  unfold denseLabels selAt
  rw [hf, List.take_length]
  exact zipIdx_filter_map _ (fun c => U.testBit c) _ 0

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit

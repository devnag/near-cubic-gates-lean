import Proof.Wire_3_5.CompilerMachineOrder
import Proof.Wire_3_5.CompilerMachinePoolContract
import Proof.Supplier.RowBinLiftCuts

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation NearCubicWires.SupplierPrinter
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut Request leftScore rightScore weight linearForm)
open NearCubicWires.ThresholdCompiler (bitInt)

/-! ## One dense child as an equation -/

/-- A dense child as a labelled equation over the two center halves (left coordinates first). -/
def eqOf {w : ℕ} (e : ExactThresholdGate (w + w)) : RowBinLift.Equation w w :=
  ⟨Sum.elim (fun i => e.weight (Fin.castAdd w i)) (fun i => e.weight (Fin.natAdd w i)), e.target⟩

/-- A dense child as a syntactic separated equation: center bit `i` is the single-bit parity `[i]`. -/
def synOf {w : ℕ} (e : ExactThresholdGate (w + w)) : SynEq :=
  (⟨-e.target, (List.finRange w).map fun i => (e.weight (Fin.castAdd w i), [i.val], false)⟩,
   ⟨0, (List.finRange w).map fun i => (e.weight (Fin.natAdd w i), [i.val], false)⟩)

theorem eval_half {w : ℕ} (c : ℤ) (f : Fin w → ℤ) (z : ℕ) :
    (⟨c, (List.finRange w).map fun i => (f i, [i.val], false)⟩ : HalfScore).eval z =
      c + ∑ i, f i * bitInt (z.testBit i.val) := by
  simp only [HalfScore.eval, List.map_map]
  congr 1
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : z.testBit i.val <;> simp [parityOf, bitInt, h]

/-- **A dense child's syntactic value is its equation's difference** at the center assignment `(a_L, a_R)`. -/
theorem synOf_value {w : ℕ} (e : ExactThresholdGate (w + w)) (aL aR : ℕ) :
    (synOf e).value aL aR = (eqOf e).difference (RowBinLift.assignment aL aR) := by
  simp only [SynEq.value, synOf, eval_half, LabelledEquation.difference, LabelledEquation.score, eqOf,
    Fintype.sum_sum_type, RowBinLift.assignment, Sum.elim_inl, Sum.elim_inr]
  ring

/-- **The equation holds exactly where the dense child holds** at the center input `(a_L, a_R)`. -/
theorem eqOf_holds {w : ℕ} (e : ExactThresholdGate (w + w)) (aL aR : ℕ) :
    decide ((eqOf e).Holds (RowBinLift.assignment aL aR)) = e.eval (centerInput w aL aR) := by
  unfold ExactThresholdGate.eval
  apply decide_eq_decide.mpr
  have h1 : ∀ i : Fin w, centerInput w aL aR (Fin.castAdd w i) = aL.testBit i.val := by
    intro i
    simp [centerInput, i.isLt]
  have h2 : ∀ i : Fin w, centerInput w aL aR (Fin.natAdd w i) = aR.testBit i.val := by
    intro i
    simp [centerInput]
  simp only [LabelledEquation.Holds, LabelledEquation.difference, LabelledEquation.score, eqOf,
    Fintype.sum_sum_type, RowBinLift.assignment, Sum.elim_inl, Sum.elim_inr, sub_eq_zero, Fin.sum_univ_add, h1, h2]
  rfl

/-- The stacked syntactic equation of dense children has the value of base's stacked labelled equation. -/
theorem stackSyn_value {w : ℕ} (H : ℤ) (aL aR : ℕ) : ∀ es : List (ExactThresholdGate (w + w)),
    (stackSyn H (es.map synOf)).value aL aR =
      (stackEquations H (es.map eqOf)).difference (RowBinLift.assignment aL aR)
  | [] => by simp [stackSyn, zeroSyn, SynEq.value, HalfScore.eval]
  | e :: es => by
    rw [List.map_cons, List.map_cons, stackEquations_difference_cons, ← stackSyn_value H aL aR es, ← synOf_value]
    simp only [stackSyn, SynEq.value, eval_addH, eval_scaleH]
    ring

/-! ## Labels and the pool as syntactic equations -/

/-- The dense children of the labels of a mask, in increasing label order. -/
def denseLabels {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (U : ℕ) : List (ExactThresholdGate (w + w)) :=
  (D.flatten.zipIdx.filter fun ec => U.testBit ec.2).map Prod.fst

/-- The pool as syntactic separated equations. -/
def poolSyn {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) : List (List SynEq) := D.map (List.map synOf)

theorem zipIdx_filter_map {α β : Type} (f : α → β) (p : ℕ → Bool) : ∀ (l : List α) (n : ℕ),
    (((l.map f).zipIdx n).filter fun ec => p ec.2).map Prod.fst =
      (((l.zipIdx n).filter fun ec => p ec.2).map Prod.fst).map f
  | [], _ => rfl
  | a :: l, n => by
    simp only [List.map_cons, List.zipIdx_cons, List.filter_cons]
    split_ifs <;> simp [zipIdx_filter_map f p l (n + 1)]

theorem eqsOfMask_poolSyn {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (U : ℕ) :
    eqsOfMask (poolSyn D) U = (denseLabels D U).map synOf := by
  unfold eqsOfMask denseLabels poolSyn
  rw [← List.map_flatten]
  exact zipIdx_filter_map synOf (fun c => U.testBit c) D.flatten 0

theorem labelsOf_congr (p1 p2 : List (List SynEq)) (h : p1.map List.length = p2.map List.length) (a : ℕ) :
    labelsOf p1 a = labelsOf p2 a := by
  unfold labelsOf
  have h1 : (p1.take a).map List.length = (p2.take a).map List.length := by
    rw [List.map_take, List.map_take, h]
  have h2 : (p1.getD a []).length = (p2.getD a []).length := by
    have hl : p1.length = p2.length := by simpa using congrArg List.length h
    by_cases ha : a < p1.length
    · rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ (by omega)]
      have := congrArg (fun l => l[a]?) h
      simp only [List.getElem?_map, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem (show a < p2.length by omega),
        Option.map_some, Option.some.injEq] at this
      exact this
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  rw [h1, h2]

theorem monoMasks_congr (p1 p2 : List (List SynEq)) (h : p1.map List.length = p2.map List.length) :
    ∀ mono : List ℕ, monoMasks p1 mono = monoMasks p2 mono
  | [] => rfl
  | a :: as => by
    simp only [monoMasks, labelsOf_congr p1 p2 h a, monoMasks_congr p1 p2 h as]

theorem oddMasksM_congr (p1 p2 : List (List SynEq)) (h : p1.map List.length = p2.map List.length) (p : F2Poly ℕ) :
    oddMasksM p1 p = oddMasksM p2 p := by
  unfold oddMasksM
  have : monoMasks p1 = monoMasks p2 := funext (monoMasks_congr p1 p2 h)
  rw [this]

theorem shape_poolSyn {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) :
    (shapeOf D).map List.length = (poolSyn D).map List.length := by
  simp [shapeOf, poolSyn, List.map_map, Function.comp_def]

/-! ## The stacked cuts -/

def occCut {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H v : ℤ) (e : ℕ × ℕ) : Cut :=
  RowBinLift.split (v * (-2) ^ (e.1 - 1)) (stackEquations H ((denseLabels D e.2).map eqOf))

/-- The cuts of one term under counter value `j` (as `termOcc`). -/
def termCuts {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H : ℤ) (Q : ℕ) (t : ℤ × List (F2Poly ℕ))
    (j : ℕ) : List Cut :=
  (unionsM Q (oddMasksM (shapeOf D) (selectBits t.2 j).flatten)).map
    (occCut D H (t.1 * 2 ^ 0 * -(-1 : ℤ) ^ (selectBits t.2 j).length))

/-- **The compiler stages' cuts in the machine's order**: for each counter value `j < 2^m`, for each term, the
stacked cut of every lifted occurrence. -/
def cutsRefX {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) :
    List Cut :=
  (List.range (2 ^ m)).flatMap fun j => V.flatMap fun t => termCuts D H Q t j

theorem occ_value {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H v : ℤ) (e : ℕ × ℕ) (aL aR : ℕ) :
    (if (occOf (poolSyn D) H v e).left.eval aL + (occOf (poolSyn D) H v e).right.eval aR = 0 then
      (occOf (poolSyn D) H v e).v else 0) = EquationRow.exactValue (occCut D H v e) aL aR := by
  rw [occCut, RowBinLift.split_value]
  have hv : (occOf (poolSyn D) H v e).left.eval aL + (occOf (poolSyn D) H v e).right.eval aR =
      (stackEquations H ((denseLabels D e.2).map eqOf)).difference (RowBinLift.assignment aL aR) := by
    show (conjSyn (poolSyn D) H e.2).value aL aR = _
    rw [conjSyn, eqsOfMask_poolSyn, stackSyn_value]
  rw [hv]
  show _ = _ * ((decide ((stackEquations H ((denseLabels D e.2).map eqOf)).difference
    (RowBinLift.assignment aL aR) = 0)).toNat : ℤ)
  by_cases h0 : (stackEquations H ((denseLabels D e.2).map eqOf)).difference (RowBinLift.assignment aL aR) = 0
  · simp [h0, occOf]
  · simp [h0]

/-- **The cuts' exact values are the occurrence table of `compileRefX` over the pool** (at every center assignment). -/
theorem occTable_cutsRefX {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H : ℤ) (m Q : ℕ)
    (V : IntExpression ℕ) (aL aR : ℕ) :
    occTable (compileRefX (poolSyn D) H m Q V) aL aR =
      ((cutsRefX D H m Q V).map fun c => EquationRow.exactValue c aL aR).sum := by
  unfold occTable compileRefX cutsRefX
  congr 1
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  apply List.flatMap_congr
  intro t _
  unfold termOcc termCuts
  rw [oddMasksM_congr (shapeOf D) (poolSyn D) (shape_poolSyn D), List.map_map, List.map_map]
  apply List.map_congr_left
  intro e _
  exact occ_value D H _ e aL aR

/-! ## The printer's table of a doubled request -/

/-- **The printer's table of a request whose cuts are `doubled false cs`** is the sum of the exact values of `cs` at
the center bits `φ(row), φ(col)` (base's `request_value`, with the general row transform `φ`). -/
theorem table_doubled (r : Request) (cs : List Cut) (hr : r.cuts = EquationRow.doubled false cs)
    (row col : Fin r.U) :
    weightedDominance (leftScore r) (rightScore r) (weight r) row col =
      (cs.map fun c => EquationRow.exactValue c (r.phi row.val) (r.phi col.val)).sum := by
  calc
    _ = ∑ i : Fin r.Gates, EquationRow.weakValue (r.cuts.get i) (r.phi row.val) (r.phi col.val) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold EquationRow.weakValue
      rw [threshold_split_as_dominance]
      rfl
    _ = (r.cuts.map fun c => EquationRow.weakValue c (r.phi row.val) (r.phi col.val)).sum := by
      rw [← List.sum_ofFn]
      change (List.ofFn (fun i : Fin r.cuts.length =>
        EquationRow.weakValue r.cuts[i.val] (r.phi row.val) (r.phi col.val))).sum = _
      have h := List.map_ofFn (f := fun i : Fin r.cuts.length => r.cuts[i.val])
        (g := fun c => EquationRow.weakValue c (r.phi row.val) (r.phi col.val))
      rw [List.ofFn_getElem] at h
      exact congrArg List.sum h.symm
    _ = _ := by rw [hr]; exact EquationRow.doubled_value false cs _ _

end NearCubicWires.WireExponent3_5.CompilerMachine.Req

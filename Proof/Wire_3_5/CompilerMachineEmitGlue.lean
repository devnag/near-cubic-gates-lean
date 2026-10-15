import Proof.Wire_3_5.CompilerMachineEmitGroups
import Proof.Wire_3_5.CompilerMachinePolySubset

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.Poly (cbits groupWord groupOf groupsRef)
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut cutWord signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- The groups' data: one `(counter value, term)` per group, in `groupsRef`'s order. -/
def xsOf (m : ℕ) (V : IntExpression ℕ) : List (ℕ × (ℤ × List (F2Poly ℕ))) :=
  (List.range (2 ^ m)).flatMap fun j => V.map fun t => (j, t)

theorem groupsRef_eq (Q : ℕ) (pool : List (List SynEq)) (m : ℕ) (V : IntExpression ℕ) :
    groupsRef Q pool m V = (xsOf m V).flatMap fun x => groupOf Q pool x.1 x.2 := by
  simp [groupsRef, xsOf, List.flatMap_assoc, List.flatMap_map]

theorem cutsRefX_eq' {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) :
    cutsRefX D H m Q V = (xsOf m V).flatMap fun x => termCuts D H Q x.2 x.1 := by
  simp [cutsRefX, xsOf, List.flatMap_assoc, List.flatMap_map]

theorem stackRecs_tail (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n))
    (r : ℕ) (hr : r < 2 * (width + width + 1)) :
    ((stackRecs h side width L).getD r []).tail = (stackBits h side width L).getD r [] := by
  rw [stackRecs_bits, List.getD_eq_getElem _ _ (by simpa [stackBits_length] using hr), List.getElem_map,
    List.getD_eq_getElem _ _ (by simpa [stackBits_length] using hr)]
  rfl

/-- The machine's signed field `q` is field `q` of the stacked equation (`stack_value`). -/
theorem fz_eq_fieldOf (h : ℕ) {n : ℕ} (side : List Bool) (width : ℕ) (L : List (List Bool × ExactThresholdGate n))
    (q : ℕ) (hq : q < width + width + 1)
    (hL : ∀ fe ∈ L, (fieldPN side fe.1 width fe.2 q).1 < 2 ^ h ∧ (fieldPN side fe.1 width fe.2 q).2 < 2 ^ h) :
    fz (stackBits h side width L) q =
      fieldOf (SupplierPipeline.stackEquations (2 ^ h) (L.map fun fe => eqOf (pullDense side fe.1 width fe.2))) q := by
  have := stack_value h side width q hq L hL
  rw [stackRecs_tail h side width L (2 * q) (by omega), stackRecs_tail h side width L (2 * q + 1) (by omega)] at this
  exact this

theorem mem_selAt {α : Type} (PC : List α) (U j : ℕ) (x : α) (hx : x ∈ selAt PC U j) : x ∈ PC := by
  unfold selAt at hx
  obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hx
  exact List.mem_of_mem_take (List.fst_mem_of_mem_zipIdx (List.mem_filter.mp hec).1)

theorem unionsM_pos (Q : ℕ) (G : List ℕ) : ∀ e ∈ unionsM Q G, 1 ≤ e.1 := by
  have key : ∀ (G : List ℕ) (E : List (ℕ × ℕ)), (∀ e ∈ E, 1 ≤ e.1) → ∀ e ∈ G.foldl (liftStep Q) E, 1 ≤ e.1 := by
    intro G
    induction G with
    | nil => intro E hE; simpa using hE
    | cons g G ih =>
      intro E hE
      rw [List.foldl_cons]
      apply ih
      intro e he
      unfold liftStep at he
      simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
      rcases he with (he | ⟨e', ⟨he', _⟩, rfl⟩) | he
      · exact hE e he
      · show 1 ≤ e'.1 + 1; omega
      · split_ifs at he
        · simp only [List.mem_singleton] at he; subst he; simp
        · simp at he
  exact key G [] (by simp)

/-- **One lifted occurrence**: the machine's words are the two successor cuts of the stacked cut. -/
theorem entryOut_eq (h width p : ℕ) {n : ℕ} (side : List Bool) (a : DecompositionAlgorithm)
    (gates : List (SupportedNormalizedGate n)) (flips : List (List Bool)) (c : ℤ) (L : ℕ) (e : ℕ × ℕ) (hk1 : 1 ≤ e.1)
    (hPN : ∀ fe ∈ poolChildren a gates flips, ∀ q, q ≤ width + width →
      (fieldPN side fe.1 width fe.2 q).1 < 2 ^ h ∧ (fieldPN side fe.1 width fe.2 q).2 < 2 ^ h) :
    (EquationRow.doubled false [occCut (densePool a gates side width flips) (2 ^ h) (c * 2 ^ 0 * -(-1 : ℤ) ^ L) e]).flatMap
        (cutWord (p + 1)) =
      entryOut h width (p + 1) side (poolChildren a gates flips) c (decide (L % 2 = 1)) e := by
  set PC := poolChildren a gates flips
  set sel := selAt PC e.2 PC.length
  set E' := SupplierPipeline.stackEquations (2 ^ h) (sel.map fun fe => eqOf (pullDense side fe.1 width fe.2))
  have hocc : occCut (densePool a gates side width flips) (2 ^ h) (c * 2 ^ 0 * -(-1 : ℤ) ^ L) e =
      RowBinLift.split (coefVal c L e.1) E' := by
    unfold occCut coefVal
    rw [denseLabels_eq gates side width flips e.2 a, List.map_map]
    rfl
  rw [hocc, cutPair_eq]
  have hsel : ∀ fe ∈ sel, ∀ q, q ≤ width + width →
      (fieldPN side fe.1 width fe.2 q).1 < 2 ^ h ∧ (fieldPN side fe.1 width fe.2 q).2 < 2 ^ h :=
    fun fe hfe q hq => hPN fe (mem_selAt PC e.2 PC.length fe hfe) q hq
  have hfz : ∀ q, q < width + width + 1 → fz (stackBits h side width sel) q = fieldOf E' q :=
    fun q hq => fz_eq_fieldOf h side width sel q hq (fun fe hfe => hsel fe hfe q (by omega))
  have hfw : ∀ j, j ≤ width + width + 1 →
      fieldsWord (p + 1) (stackBits h side width sel) j = (List.range j).flatMap (fun q => sm p (fieldOf E' q)) := by
    intro j hj
    unfold fieldsWord sm
    apply List.flatMap_congr
    intro q hq
    rw [hfz q (by simp at hq; omega)]
  unfold entryOut entryWords
  rw [hfw (width + width + 1) le_rfl, hfw (width + width) (by omega), hfz (width + width) (by omega), List.range_succ,
    List.flatMap_append]
  have c1 : frame ((decide (c ≠ 0) && (decide (c < 0) ^^ decide (L % 2 = 1) ^^ decide (e.1 % 2 = 1))) ::
      binary (p + 1) (c.natAbs * 2 ^ (e.1 - 1))) = sm p (coefVal c L e.1) := by
    unfold sm; rw [coef_sm p c L e.1 hk1]
  have c2 : frame ((decide (c ≠ 0) && !(decide (c < 0) ^^ decide (L % 2 = 1) ^^ decide (e.1 % 2 = 1))) ::
      binary (p + 1) (c.natAbs * 2 ^ (e.1 - 1))) = sm p (-coefVal c L e.1) := by
    unfold sm; rw [coef_sm_neg p c L e.1 hk1]
  rw [c1, c2]
  simp [sm, List.append_assoc]

/-- **All groups**: the machine's words (per group, per entry, in `groupsRef`'s order) are the C3 v2 reference's cut
words. -/
theorem emit_words_eq (h width p : ℕ) {n : ℕ} (side : List Bool) (a : DecompositionAlgorithm)
    (gates : List (SupportedNormalizedGate n)) (flips : List (List Bool)) (m Q : ℕ) (V : IntExpression ℕ)
    (hPN : ∀ fe ∈ poolChildren a gates flips, ∀ q, q ≤ width + width →
      (fieldPN side fe.1 width fe.2 q).1 < 2 ^ h ∧ (fieldPN side fe.1 width fe.2 q).2 < 2 ^ h) :
    (EquationRow.doubled false (cutsRefX (densePool a gates side width flips) (2 ^ h) m Q V)).flatMap (cutWord (p + 1)) =
      (xsOf m V).flatMap fun x =>
        (unionsM Q (oddMasksM (shapeOf (densePool a gates side width flips)) (selectBits x.2.2 x.1).flatten)).flatMap
          (entryOut h width (p + 1) side (poolChildren a gates flips) x.2.1
            (decide ((selectBits x.2.2 x.1).length % 2 = 1))) := by
  rw [cutsRefX_eq']
  unfold EquationRow.doubled
  simp only [List.flatMap_assoc]
  apply List.flatMap_congr
  intro x _
  unfold termCuts
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro e he
  rw [← entryOut_eq h width p side a gates flips x.2.1 (selectBits x.2.2 x.1).length e (unionsM_pos Q _ e he) hPN]
  simp [EquationRow.doubled]

theorem emit_count_eq {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) :
    (cutsRefX D H m Q V).length =
      ((xsOf m V).map fun x => (unionsM Q (oddMasksM (shapeOf D) (selectBits x.2.2 x.1).flatten)).length).sum := by
  rw [cutsRefX_eq', List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro x _
  simp [termCuts]

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit

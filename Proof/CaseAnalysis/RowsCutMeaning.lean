import Proof.CaseAnalysis.RowsCacheInput

/-! The actual tuple-cut bytes are precisely the common-width row's cuts.
All degree and monomial occurrences remain in their enumerated order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCutMeaning
open RepairRepresentation SupplierPipeline MatrixScoreBatch RowBinLift
open CloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem coordinates_stack {l r : ℕ} (b : ℤ)
    (es : List (LabelledEquation (Fin (l+r)))) :
    coordinates (stackEquations b es)=stackEquations b (es.map coordinates) := by
  induction es with
  | nil =>
    simp only [List.map_nil,stackEquations,coordinates]
    congr 1
    funext i
    cases i <;> rfl
  | cons e es ih =>
    simp only [List.map_cons,stackEquations,←ih,coordinates]
    congr 1
    funext i
    cases i <;> rfl

theorem fetch_polynomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (rows : List (List Bool)) (d : ℕ) :
    RowTupleTerms.fetch (polynomial gs rows) d=monomial gs (RowTupleMaskLoop.mask rows d) := by
  simp only [RowTupleTerms.fetch,polynomial,RowTupleMaskLoop.mask,List.getElem?_map]
  cases h : rows[d]? with
  | none => simp [monomial,RowTupleCommonEquation.one,RowCachedEquation.equations,
      RowMaskMeaning.typed,RowMaskMeaning.positions]
  | some bits => rfl

theorem selected_equations {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (rows : List (List Bool)) (ds : List ℕ) :
    (RowCachedEquation.equations gs (RowTupleCommonEquation.indices gs.length rows ds)).map coordinates=
      (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [RowTupleCommonEquation.indices,List.flatMap_cons,RowCachedEquation.equations,
      List.map_append,RowTupleTerms.selectedMonomials,List.map_cons,List.flatten_cons]
    rw [fetch_polynomial]
    exact congrArg (List.append (monomial gs (RowTupleMaskLoop.mask rows d))) ih

theorem tuple_word {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p : ℕ) (rows : List (List Bool)) (ds : List ℕ) (c : ℤ) :
    RowTupleCutBody.word gs p rows ds c=cutWord p (split c
      (RowPowerBinLift.stack (RowCachedCoordinateBounds.width gs)
        (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten)) := by
  rw [cut_word,RowCoordinateLoop.equation]
  simp only [RowPowerBinLift.stack,coordinates_stack,selected_equations]

def degreeCuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (w j : ℕ) (rows : List (List Bool)) : List Cut :=
  (RowTupleSubsets.selected w rows.length (j+1)).map fun ds =>
    split ((-2 : ℤ)^j) (RowPowerBinLift.stack (RowCachedCoordinateBounds.width gs)
      (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten)

theorem degree_output {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p w j : ℕ) (rows : List (List Bool)) :
    RowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)=
      (degreeCuts gs w j rows).flatMap (cutWord p) := by
  simp only [RowTupleCutList.output,degreeCuts,List.flatMap_map]
  apply List.flatMap_congr
  intro ds _
  exact tuple_word gs p rows ds _

theorem polynomial_output {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p Q : ℕ) (rows : List (List Bool)) :
    ((List.range (min Q rows.length)).flatMap fun j =>
      RowTupleCutList.output gs p rows
        (RowTupleSubsets.selected (RowTupleSubsets.digitWidth rows.length) rows.length (j+1)) ((-2 : ℤ)^j))=
      (CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q (polynomial gs rows)).flatMap (cutWord p) := by
  simp only [CloseoutRows.orderedCuts,RowTupleTerms.terms,polynomial,List.length_map,
    List.map_flatMap,List.flatMap_assoc,List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  simpa only [degreeCuts,polynomial,List.flatMap_map] using
    degree_output gs p (RowTupleSubsets.digitWidth rows.length) j rows

end NearCubicWires.RepairOrdinary.CloseoutRowsCutMeaning

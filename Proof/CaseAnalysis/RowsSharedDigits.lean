import Proof.CaseAnalysis.RowsPolynomial

/-! One shared digit width may serve an entire live-family bank. Changing
the binary enumeration width only permutes positional subsets; no repeated
monomial or cut is removed and the matrix coordinate width is unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSharedDigits
open CloseoutRowsCutMeaning CloseoutRowsCacheInput MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (Q w : ℕ) (rows : List (List Bool)) :=
  (List.range Q).flatMap (fun j=>degreeCuts gs w j rows)

theorem degree_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (w j : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (degreeCuts gs w j rows).Perm
      (degreeCuts gs (RowTupleSubsets.digitWidth rows.length) j rows) := by
  exact ((RowTupleSubsets.selected_perm w rows.length (j+1) hw).trans
    (RowTupleSubsets.chosen_perm rows.length (j+1)).symm).map _

theorem canonical_cuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (Q : ℕ) (rows : List (List Bool)) :
    cuts gs Q (RowTupleSubsets.digitWidth rows.length) rows=
      CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q (polynomial gs rows) := by
  rw [cuts,CloseoutRowsDegreeRange.all_degrees gs Q _ rows (RowTupleSubsets.digit_fit rows.length).le]
  simp only [CloseoutRows.orderedCuts,RowTupleTerms.terms,polynomial,List.length_map,
    List.map_flatMap,List.map_map,Function.comp_def,degreeCuts]

theorem cuts_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (Q w : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (cuts gs Q w rows).Perm
      (CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q (polynomial gs rows)) := by
  rw [←canonical_cuts gs Q rows]
  apply List.Perm.flatMap_left
  intro j _
  exact degree_perm gs w j rows hw

theorem emitted_word {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (p Q w : ℕ) (rows : List (List Bool)) :
    (List.range Q).flatMap (fun j=>CloseoutRowsLoopBoundary.emitted gs p w j rows)=
      (cuts gs Q w rows).flatMap (cutWord p) := by
  simp only [CloseoutRowsLoopBoundary.emitted,degree_output,cuts,List.flatMap_assoc]

theorem batch_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (Q w : ℕ) (bank : List (List (List Bool))) (hw : ∀ rows∈bank,rows.length≤2^w) :
    (bank.flatMap (cuts gs Q w)).Perm
      (RowPowerBinLift.batch (RowCachedCoordinateBounds.width gs) Q (family gs bank)) := by
  have hp : (bank.flatMap (cuts gs Q w)).Perm
      (bank.flatMap (fun rows=>CloseoutRows.orderedCuts (RowCachedCoordinateBounds.width gs) Q (polynomial gs rows))) := by
    apply List.Perm.flatMap_left
    intro rows hr
    exact cuts_perm gs Q w rows (hw rows hr)
  exact hp.trans (by simpa only [CloseoutRows.orderedBatch,family,List.flatMap_map] using
    CloseoutRows.ordered_batch_perm (RowCachedCoordinateBounds.width gs) Q (family gs bank))

end NearCubicWires.RepairOrdinary.CloseoutRowsSharedDigits

import Proof.CaseAnalysis.RecoveryGrammarOutputScan

/-! The last paid selection and the original terminal-true reverse fold
turn the saved forward row references into the literal fixed-count grammar. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def finishStage:=Composition.machine (reselect foldRows) (fold true foldRows)
noncomputable def finishScan:=TapeEmbedding.machine 1 (TapeEmbedding.machine 1 finishStage)
def finishScanBudget (B : ℕ):=atomBudget B+1+atomBudget B

theorem finishStage_run {q bound row G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (scalars : ScalarFits q bound row W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W)
    (hg : (compileExpr b (fixedCountGrammarExpr (n:=q) count)).final.nodes.length≤G) (gw : G≤W)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B) :
    Runs finishStage (finishScanBudget B) B P source (metadata q bound row C B extra)
      (originalState (selectedFields (tag 6) q bound row C) (children b (RecoveryBoundedGrammar.rows (q:=q) count))
        graphPre stackPre (ZeroPadding.pad B (selectedWord (tag 6) q bound row C))
        (refs++references b.nodes.length (RecoveryBoundedGrammar.rows (q:=q) count)))
      (originalState (selectedFields foldRows q bound row C) (compileExpr b (fixedCountGrammarExpr (n:=q) count)).final
        graphPre stackPre (ZeroPadding.pad B (selectedWord foldRows q bound row C))
        (refs++[(compileExpr b (fixedCountGrammarExpr (n:=q) count)).output.val])) := by
  let xs:=RecoveryBoundedGrammar.rows (q:=q) count
  have hc : (children b xs).nodes.length≤G:=(children_le_combined b true xs).trans hg
  have vc:=valid.children xs hc gw
  have foldCount : (children b xs).nodes.length+(references b.nodes.length xs).length≤W := by
    rw [RecoveryBoundedGrammar.original_rows,compileExpr_length,RecoveryBoundedGrammar.all_count] at hg
    rw [children_length,RecoveryBoundedAddress.references_length]
    dsimp only [xs]
    omega
  have refBound : ∀ ref∈references b.nodes.length xs,ref≤W := by
    intro ref hr
    exact vc.values ref (List.mem_append_right refs hr)
  have foldInput : selectedFields foldRows q bound row C=RecoveryBoundedGrammarPrototype.fields C 0 0
      (references b.nodes.length xs).length 0 := by
    rw [RecoveryBoundedAddress.references_length]
    dsimp only [xs]
    rw [RecoveryBoundedGrammar.rows_length]
    rfl
  have selected:=reselect_run room scalars (tag 6) foldRows (children b xs).nodes.length
    (graphWord graphPre (children b xs)) (saved stackPre (refs++references b.nodes.length xs))
    (ZeroPadding.pad B (selectedWord (tag 6) q bound row C)) source extra (room.pad_packet_length scalars (tag 6))
  have closing:=fold_run room scalars (descriptionWidth q bound) true foldRows foldRows
    (children b xs).nodes.length (references b.nodes.length xs) (graphWord graphPre (children b xs))
    (saved stackPre refs) (ZeroPadding.pad B (selectedWord foldRows q bound row C)) source extra foldInput refBound foldCount
    (graphSupport _ hc)
    (by rw [saved_append];exact vc.support stackPre hc gw stackSupport) hs (room.pad_packet_length scalars foldRows)
  rw [saved_append,fold_original] at closing
  exact selected.join closing

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold

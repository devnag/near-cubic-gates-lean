import Proof.CaseAnalysis.RecoveryGrammarChildren

/-! Close the exact original all/any consumer from an actual finite
forward-child run. No new expression evaluator or encoded controller is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefixSize_ge_length {n : ℕ} (xs : List (BoolExpr n)) : xs.length≤prefixSize xs := by
  induction xs with
  | nil=>rfl
  | cons e xs ih=>
    have hn:=nodeCount_pos e
    simp only [List.length_cons,prefixSize]
    omega

theorem ValidReferences.children {n W G : ℕ} {b : BooleanDAGBuilder n} {refs : List ℕ}
    (h : ValidReferences b refs W) (xs : List (BoolExpr n))
    (hg : (children b xs).nodes.length≤G) (gw : G≤W) :
    ValidReferences (children b xs) (refs++references b.nodes.length xs) W := by
  constructor
  · have hp:=prefixSize_ge_length xs
    have hc:=h.count
    rw [List.length_append,RecoveryBoundedAddress.references_length,children_length]
    omega
  · intro ref hr
    rcases List.mem_append.mp hr with hr|hr
    · exact h.values ref hr
    · have hh:=saved_bound b.nodes.length xs ref hr
      rw [children_length] at hg
      omega

theorem children_run {s q bound row W C D L S B P G : ℕ}
    (room : Room W C D L S B P) (scalars : ScalarFits q bound row W)
    (p : Machine 112 s) (fuel : ℕ) (current closing next : Selection)
    (b : BooleanDAGBuilder (BoundedOracleStructuralCircuit.descriptionWidth q bound))
    (conjunction : Bool) (xs : List (BoolExpr (BoundedOracleStructuralCircuit.descriptionWidth q bound)))
    (graphPre stackPre packet source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W)
    (hg : (compileExpr b (combined conjunction xs)).final.nodes.length≤G) (gw : G≤W)
    (graphSupport : ∀ d : BooleanDAGBuilder (BoundedOracleStructuralCircuit.descriptionWidth q bound),
      d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (hclosing : selectedFields closing q bound row C=RecoveryBoundedGrammarPrototype.fields C 0 0 xs.length 0)
    (body : Runs p fuel B P source (metadata q bound row C B extra)
      (originalState (selectedFields current q bound row C) b graphPre stackPre packet refs)
      (originalState (selectedFields closing q bound row C) (children b xs) graphPre stackPre
        (ZeroPadding.pad B (selectedWord closing q bound row C)) (refs++references b.nodes.length xs))) :
    Runs (Composition.machine p (fold conjunction next)) (fuel+1+atomBudget B) B P source
      (metadata q bound row C B extra)
      (originalState (selectedFields current q bound row C) b graphPre stackPre packet refs)
      (originalState (selectedFields next q bound row C) (compileExpr b (combined conjunction xs)).final
        graphPre stackPre (ZeroPadding.pad B (selectedWord next q bound row C))
        (refs++[(compileExpr b (combined conjunction xs)).output.val])) := by
  have hc : (children b xs).nodes.length≤G:=(children_le_combined b conjunction xs).trans hg
  have vc:=valid.children xs hc gw
  have foldCount : (children b xs).nodes.length+(references b.nodes.length xs).length≤W := by
    rw [compileExpr_length,combined_count] at hg
    rw [children_length,RecoveryBoundedAddress.references_length]
    omega
  have refBound : ∀ ref∈references b.nodes.length xs,ref≤W := by
    intro ref hr
    exact vc.values ref (List.mem_append_right refs hr)
  have foldInput : selectedFields closing q bound row C=RecoveryBoundedGrammarPrototype.fields C 0 0
      (references b.nodes.length xs).length 0 := by rw [RecoveryBoundedAddress.references_length];exact hclosing
  have run:=fold_run room scalars (BoundedOracleStructuralCircuit.descriptionWidth q bound) conjunction closing next
    (children b xs).nodes.length (references b.nodes.length xs) (graphWord graphPre (children b xs))
    (saved stackPre refs) (ZeroPadding.pad B (selectedWord closing q bound row C)) source extra foldInput refBound foldCount
    (graphSupport _ hc)
    (by rw [saved_append];exact vc.support stackPre hc gw stackSupport) hs (room.pad_packet_length scalars closing)
  rw [saved_append,fold_original] at run
  exact body.join run

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold

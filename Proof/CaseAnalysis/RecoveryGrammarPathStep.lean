import Proof.CaseAnalysis.RecoveryGrammarDriverStep

/-! A literal compiled row and its paid continuation produce the next
prefix configuration of the original grammar sequence. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pathConfig {s q bound : ℕ} (p : Machine 112 s) (b : BooleanDAGBuilder (descriptionWidth q bound))
    (xs : List (BoolExpr (descriptionWidth q bound))) (current : Selection) (first C B P : ℕ)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool) (i : ℕ) :=
  (pathState b xs current first C B graphPre stackPre refs i).configuration p B P source
    (metadata q bound (first+i) C B extra)

theorem path_step_run {s q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (p : Machine 112 s) (cost : ℕ) (b : BooleanDAGBuilder (descriptionWidth q bound))
    (xs : List (BoolExpr (descriptionWidth q bound))) (current : Selection) (first i : ℕ)
    (hi : i<xs.length) (hrow : first+i<bound+1)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound))
    (core : Runs p cost B P source (metadata q bound (first+i) C B extra)
      (pathState b xs current first C B graphPre stackPre refs i)
      (originalState (selectedFields foldRows q bound (first+i) C)
        (compileExpr (children b (xs.take i)) xs[i]).final graphPre stackPre
        (ZeroPadding.pad B (selectedWord foldRows q bound (first+i) C))
        ((refs++references b.nodes.length (xs.take i))++[(compileExpr (children b (xs.take i)) xs[i]).output.val]))) :
    ∃ r,runFrom (rowBody p current) (rowBodyBudget cost B)
      (pathConfig (rowBody p current) b xs current first C B P graphPre stackPre source refs extra i)=some r ∧
      r.steps≤rowBodyBudget cost B ∧
      r.final.heads=(pathConfig (rowBody p current) b xs current first C B P graphPre stackPre source refs extra (i+1)).heads ∧
      r.final.tapes=(pathConfig (rowBody p current) b xs current first C B P graphPre stackPre source refs extra (i+1)).tapes := by
  obtain ⟨r,rr,rs,rh,rt⟩:=rowBody_run room alloc p cost (children b (xs.take i)) ⟨first+i,hrow⟩ xs[i] current current
    graphPre stackPre (ZeroPadding.pad B (selectedWord current q bound (first+i) C)) source
    (refs++references b.nodes.length (xs.take i)) extra width core
  refine ⟨r,rr,rs,?_,?_⟩
  · simpa only [pathConfig,pathState,RowState.configuration,entry,originalState,
      children_take_step b xs i hi,references_take_step b xs i hi,Nat.add_assoc,List.append_assoc] using rh
  · simpa only [pathConfig,pathState,RowState.configuration,entry,originalState,
      children_take_step b xs i hi,references_take_step b xs i hi,Nat.add_assoc,List.append_assoc] using rt

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold

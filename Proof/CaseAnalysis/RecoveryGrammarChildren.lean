import Proof.CaseAnalysis.RecoveryGrammarOriginalState

/-! The finite rows compile their original children in forward order and
then apply the already checked reverse fold. These are exact original DAG identities. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairRepresentation
open FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def children {n : ℕ} (b : BooleanDAGBuilder n) : List (BoolExpr n)→BooleanDAGBuilder n
  | []=>b
  | e::xs=>children (compileExpr b e).final xs

theorem children_length {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) :
    (children b xs).nodes.length=b.nodes.length+prefixSize xs := by
  induction xs generalizing b with
  | nil=>simp only [children,prefixSize,Nat.add_zero]
  | cons e xs ih=>simp only [children,ih,compileExpr_length,prefixSize,Nat.add_assoc]

theorem children_nodes {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) :
    (children b xs).nodes=b.nodes++prefixNodes b.nodes.length xs := by
  induction xs generalizing b with
  | nil=>simp only [children,prefixNodes,List.append_nil]
  | cons e xs ih=>
    rw [children,ih,(compileExpr b e).extension.nodes_eq,compileExpr_nodes]
    simp only [List.length_append,exprNodes_length,prefixNodes,List.append_assoc]

def combined {n : ℕ} (conjunction : Bool) (xs : List (BoolExpr n)) : BoolExpr n:=
  if conjunction then BoolExpr.all xs else BoolExpr.any xs
theorem combined_count {n : ℕ} (conjunction : Bool) (xs : List (BoolExpr n)) :
    (combined conjunction xs).nodeCount=prefixSize xs+xs.length+1 := by
  cases conjunction
  · exact any_count xs
  · exact RecoveryBoundedGrammar.all_count xs
theorem combined_nodes {n : ℕ} (conjunction : Bool) (base : ℕ) (xs : List (BoolExpr n)) :
    exprNodes base (combined conjunction xs)=prefixNodes base xs++[BooleanNode.const conjunction]++
      foldNodes conjunction (base+prefixSize xs) (references base xs).reverse := by
  cases conjunction
  · exact any_nodes base xs
  · exact RecoveryBoundedGrammar.all_nodes base xs

theorem children_le_combined {n : ℕ} (b : BooleanDAGBuilder n) (conjunction : Bool) (xs : List (BoolExpr n)) :
    (children b xs).nodes.length≤(compileExpr b (combined conjunction xs)).final.nodes.length := by
  rw [children_length,compileExpr_length,combined_count]
  omega

theorem fold_original {n : ℕ} (b : BooleanDAGBuilder n) (conjunction : Bool) (xs : List (BoolExpr n))
    (graphPre stackPre packet : List Bool) (refs : List ℕ) (fields : Fin 78→List Bool) :
    foldState n conjunction (children b xs).nodes.length (references b.nodes.length xs)
      (graphWord graphPre (children b xs)) (saved stackPre refs) packet fields=
      originalState fields (compileExpr b (combined conjunction xs)).final graphPre stackPre packet
        (refs++[(compileExpr b (combined conjunction xs)).output.val]) := by
  have size : (compileExpr b (combined conjunction xs)).final.nodes.length=
      (children b xs).nodes.length+(references b.nodes.length xs).length+1 := by
    rw [compileExpr_length,combined_count,children_length,RecoveryBoundedAddress.references_length]
    omega
  have ref : (compileExpr b (combined conjunction xs)).output.val=
      (children b xs).nodes.length+(references b.nodes.length xs).length := by
    rw [compileExpr_output,combined_count,children_length,RecoveryBoundedAddress.references_length]
    omega
  have graph : graphWord graphPre (compileExpr b (combined conjunction xs)).final=
      graphWord graphPre (children b xs)++([BooleanNode.const conjunction]++
        foldNodes (n:=n) conjunction (children b xs).nodes.length (references b.nodes.length xs).reverse).flatMap
        PCPPRequestNodeSchema.native := by
    unfold graphWord
    rw [(compileExpr b (combined conjunction xs)).extension.nodes_eq,compileExpr_nodes,combined_nodes,
      children_length,children_nodes]
    simp only [List.flatMap_append,List.append_assoc]
  unfold foldState originalState
  rw [ref,size,graph,←saved_push]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold

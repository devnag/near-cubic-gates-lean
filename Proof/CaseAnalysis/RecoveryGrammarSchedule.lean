import Proof.CaseAnalysis.RecoveryGrammarLessShortcut

/-! The literal original grammar has the same forward-child/reverse-fold
schedule already executed by the original address and unary workers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammar
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem all_count {n : ℕ} (xs : List (BoolExpr n)) :
    (BoolExpr.all xs).nodeCount=prefixSize xs+xs.length+1 := by
  induction xs with
  | nil=>rfl
  | cons e xs ih=>
    simp only [BoolExpr.all,BoolExpr.nodeCount,prefixSize,List.length_cons,ih]
    omega

theorem all_nodes {n : ℕ} (base : ℕ) (xs : List (BoolExpr n)) :
    exprNodes base (BoolExpr.all xs)=prefixNodes base xs++[BooleanNode.const true]++
      foldNodes true (base+prefixSize xs) (references base xs).reverse := by
  induction xs generalizing base with
  | nil=>rfl
  | cons e xs ih=>
    rw [BoolExpr.all,exprNodes,ih,references,List.reverse_cons,foldNodes_append,
      List.length_reverse,RecoveryBoundedAddress.references_length,all_count]
    simp only [prefixNodes,prefixSize,foldNodes,List.append_assoc]
    have he : base+e.nodeCount+prefixSize xs=base+(e.nodeCount+prefixSize xs) := by omega
    rw [he]
    have hf : base+e.nodeCount+(prefixSize xs+xs.length+1)-1=
        base+(e.nodeCount+prefixSize xs)+xs.length := by omega
    rw [hf]
    rfl

theorem all_suffix {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) :
    (compileExpr b (BoolExpr.all xs)).extension.suffix=
      prefixNodes b.nodes.length xs++[BooleanNode.const true]++
        foldNodes true (b.nodes.length+prefixSize xs) (references b.nodes.length xs).reverse := by
  rw [compileExpr_nodes,all_nodes]

theorem prefixSize_append {n : ℕ} (xs ys : List (BoolExpr n)) :
    prefixSize (xs++ys)=prefixSize xs+prefixSize ys := by
  induction xs with
  | nil=>simp only [List.nil_append,prefixSize,Nat.zero_add]
  | cons x xs ih=>simp only [List.cons_append,prefixSize,ih,Nat.add_assoc]

theorem prefixNodes_append {n : ℕ} (base : ℕ) (xs ys : List (BoolExpr n)) :
    prefixNodes base (xs++ys)=prefixNodes base xs++prefixNodes (base+prefixSize xs) ys := by
  induction xs generalizing base with
  | nil=>simp only [List.nil_append,prefixNodes,prefixSize,Nat.add_zero]
  | cons x xs ih=>simp only [List.cons_append,prefixNodes,ih,prefixSize,Nat.add_assoc,List.append_assoc]

theorem references_append {n : ℕ} (base : ℕ) (xs ys : List (BoolExpr n)) :
    references base (xs++ys)=references base xs++references (base+prefixSize xs) ys := by
  induction xs generalizing base with
  | nil=>simp only [List.nil_append,references,prefixSize,Nat.add_zero]
  | cons x xs ih=>simp only [List.cons_append,references,ih,prefixSize,Nat.add_assoc]

def rows {q bound : ℕ} (count : Fin bound) : List (BoolExpr (descriptionWidth q bound)) :=
  countNodeRows count++outputRowExpr ⟨count.val+1,by omega⟩::countPaddingRows count

theorem original_rows {q bound : ℕ} (count : Fin bound) :
    fixedCountGrammarExpr (n:=q) count=BoolExpr.all (rows (q:=q) count) := rfl

theorem rows_length {q bound : ℕ} (count : Fin bound) :
    (rows (q:=q) count).length=bound+1 := by
  simp only [rows,countNodeRows,countPaddingRows,List.length_append,List.length_cons,List.length_ofFn]
  have hc:=count.isLt
  omega

theorem original_suffix {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (count : Fin bound) :
    (compileExpr b (fixedCountGrammarExpr (n:=q) count)).extension.suffix=
      prefixNodes b.nodes.length (rows (q:=q) count)++[BooleanNode.const true]++
        foldNodes true (b.nodes.length+prefixSize (rows (q:=q) count))
          (references b.nodes.length (rows (q:=q) count)).reverse := by
  rw [original_rows,all_suffix]

theorem original_output {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (count : Fin bound) :
    (compileExpr b (fixedCountGrammarExpr (n:=q) count)).output.val=
      b.nodes.length+prefixSize (rows (q:=q) count)+bound+1 := by
  rw [original_rows,compileExpr_output,all_count,rows_length]
  omega

theorem rows_fit {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (count : Fin bound) (W : ℕ)
    (h : (compileExpr b (fixedCountGrammarExpr (n:=q) count)).final.nodes.length ≤ W) :
    bound+1 ≤ W ∧ b.nodes.length+prefixSize (rows (q:=q) count)+bound+1 ≤ W ∧
      ∀ ref∈references b.nodes.length (rows (q:=q) count),ref ≤ W := by
  rw [original_rows,compileExpr_length,all_count,rows_length] at h
  refine ⟨by omega,by omega,?_⟩
  intro ref hr
  have hs:=RecoveryBoundedAddress.saved_bound b.nodes.length (rows (q:=q) count) ref hr
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammar

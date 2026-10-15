import Proof.CaseAnalysis.RecoveryGrammarRepeat

/-! Prefix identities for the literal original forward row sequence.
These expose the exact builders and saved references used by the finite driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open SourceInterfaces FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem children_append {n : ℕ} (b : BooleanDAGBuilder n) (xs ys : List (BoolExpr n)) :
    children b (xs++ys)=children (children b xs) ys := by
  induction xs generalizing b with
  | nil=>rfl
  | cons x xs ih=>simp only [List.cons_append,children,ih]

theorem children_take_step {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) (i : ℕ) (hi : i<xs.length) :
    children b (xs.take (i+1))=(compileExpr (children b (xs.take i)) xs[i]).final := by
  rw [List.take_succ_eq_append_getElem hi,children_append]
  rfl

theorem children_take_le {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) (i : ℕ) :
    (children b (xs.take i)).nodes.length≤(children b xs).nodes.length := by
  rw [children_length,children_length]
  have h:=RecoveryBoundedGrammar.prefixSize_append (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at h
  omega

theorem references_take_step {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) (i : ℕ) (hi : i<xs.length) :
    references b.nodes.length (xs.take (i+1))=
      references b.nodes.length (xs.take i)++[(compileExpr (children b (xs.take i)) xs[i]).output.val] := by
  rw [List.take_succ_eq_append_getElem hi,RecoveryBoundedGrammar.references_append,
    compileExpr_output,children_length]
  rfl

def pathState {q bound : ℕ} (b : BooleanDAGBuilder (BoundedOracleStructuralCircuit.descriptionWidth q bound))
    (xs : List (BoolExpr (BoundedOracleStructuralCircuit.descriptionWidth q bound)))
    (current : Selection) (first C B : ℕ) (graphPre stackPre : List Bool) (refs : List ℕ) (i : ℕ) :=
  originalState (selectedFields current q bound (first+i) C) (children b (xs.take i)) graphPre stackPre
    (ZeroPadding.pad B (selectedWord current q bound (first+i) C)) (refs++references b.nodes.length (xs.take i))

theorem pathState_zero {q bound : ℕ} (b : BooleanDAGBuilder (BoundedOracleStructuralCircuit.descriptionWidth q bound))
    (xs : List (BoolExpr (BoundedOracleStructuralCircuit.descriptionWidth q bound)))
    (current : Selection) (first C B : ℕ) (graphPre stackPre : List Bool) (refs : List ℕ) :
    pathState b xs current first C B graphPre stackPre refs 0=
      originalState (selectedFields current q bound first C) b graphPre stackPre
        (ZeroPadding.pad B (selectedWord current q bound first C)) refs := by
  simp only [pathState,Nat.add_zero,List.take_zero,children,references,List.append_nil]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold

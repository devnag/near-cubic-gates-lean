import Proof.CaseAnalysis.RecoveryGuardedBudget

/-! The actual original guarded selector consists of its forward guarded
heads, one false seed, and the reverse OR fold. Shared wire references are
retained numerically; no described computation is expanded. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversal
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixSize {n : ℕ} : List (BoolExpr n × ℕ)→ℕ
  | []=>0
  | (e,_)::rest=>e.nodeCount+1+prefixSize rest
def prefixNodes {n : ℕ} (base : ℕ) : List (BoolExpr n × ℕ)→List (BooleanNode n)
  | []=>[]
  | (e,value)::rest=>exprNodes base e++[.and (base+e.nodeCount-1) value]++
      prefixNodes (base+e.nodeCount+1) rest
def references {n : ℕ} (base : ℕ) : List (BoolExpr n × ℕ)→List ℕ
  | []=>[]
  | (e,_)::rest=>(base+e.nodeCount)::references (base+e.nodeCount+1) rest

theorem references_length {n : ℕ} (base : ℕ) (xs : List (BoolExpr n × ℕ)) :
    (references base xs).length=xs.length := by
  induction xs generalizing base with
  | nil=>rfl
  | cons x xs ih=>simp [references,ih]

theorem guardCount_prefix {n : ℕ} (xs : List (BoolExpr n × ℕ)) :
    guardCount xs=prefixSize xs+xs.length+1 := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    rcases x with ⟨e,v⟩
    simp only [guardCount,prefixSize,List.length_cons,ih]
    omega

theorem guardNodes_forward_reverse {n : ℕ} (base : ℕ) (xs : List (BoolExpr n × ℕ)) :
    guardNodes base xs=prefixNodes base xs++[BooleanNode.const false]++
      foldNodes false (base+prefixSize xs) (references base xs).reverse := by
  induction xs generalizing base with
  | nil=>rfl
  | cons x xs ih=>
    rcases x with ⟨e,v⟩
    rw [guardNodes,ih,references,List.reverse_cons,foldNodes_append,List.length_reverse,references_length,
      guardCount_prefix]
    simp only [prefixNodes,prefixSize,foldNodes,List.append_assoc]
    have baseEq : base+e.nodeCount+1+prefixSize xs=base+(e.nodeCount+1+prefixSize xs) := by omega
    rw [baseEq]
    have endEq : base+e.nodeCount+1+(prefixSize xs+xs.length+1)-1=
        base+(e.nodeCount+1+prefixSize xs)+xs.length := by omega
    rw [endEq]
    rfl

theorem field_select_suffix {n bound : ℕ}
    (b : BooleanDAGBuilder (descriptionWidth n bound))
    (field : Fin (bound+1)→ℕ→BoolExpr (descriptionWidth n bound))
    (row : Fin (bound+1)) (values : List (LiveWire b)) :
    (compileFieldSelect b field row values).extension.suffix=
      prefixNodes b.nodes.length (choices (fieldChoices field row values))++[BooleanNode.const false]++
      foldNodes false (b.nodes.length+prefixSize (choices (fieldChoices field row values)))
        (references b.nodes.length (choices (fieldChoices field row values))).reverse := by
  change (compileGuardedAny b (fieldChoices field row values)).extension.suffix=_
  rw [compileGuardedAny_nodes,guardNodes_forward_reverse]

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversal

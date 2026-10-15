import Proof.CaseAnalysis.RecoveryUniversalPrefix

/-! The original constant-address expression uses plain child expressions,
then a false seed and the reverse OR fold. No guarded AND nodes are inserted. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixSize {n : ℕ} : List (BoolExpr n)→ℕ
  | []=>0
  | e::rest=>e.nodeCount+prefixSize rest
def prefixNodes {n : ℕ} (base : ℕ) : List (BoolExpr n)→List (BooleanNode n)
  | []=>[]
  | e::rest=>exprNodes base e++prefixNodes (base+e.nodeCount) rest
def references {n : ℕ} (base : ℕ) : List (BoolExpr n)→List ℕ
  | []=>[]
  | e::rest=>(base+e.nodeCount-1)::references (base+e.nodeCount) rest

theorem references_length {n : ℕ} (base : ℕ) (xs : List (BoolExpr n)) :
    (references base xs).length=xs.length := by
  induction xs generalizing base with
  | nil=>rfl
  | cons e xs ih=>simp only [references,List.length_cons,ih]

theorem any_count {n : ℕ} (xs : List (BoolExpr n)) :
    (BoolExpr.any xs).nodeCount=prefixSize xs+xs.length+1 := by
  induction xs with
  | nil=>rfl
  | cons e xs ih=>
    simp only [BoolExpr.any,BoolExpr.nodeCount,prefixSize,List.length_cons,ih]
    omega

theorem any_nodes {n : ℕ} (base : ℕ) (xs : List (BoolExpr n)) :
    exprNodes base (BoolExpr.any xs)=prefixNodes base xs++[BooleanNode.const false]++
      foldNodes false (base+prefixSize xs) (references base xs).reverse := by
  induction xs generalizing base with
  | nil=>rfl
  | cons e xs ih=>
    rw [BoolExpr.any,exprNodes,ih,references,List.reverse_cons,foldNodes_append,
      List.length_reverse,references_length,any_count]
    simp only [prefixNodes,prefixSize,foldNodes,List.append_assoc]
    have he : base+e.nodeCount+prefixSize xs=base+(e.nodeCount+prefixSize xs) := by omega
    rw [he]
    have hf : base+e.nodeCount+(prefixSize xs+xs.length+1)-1=
        base+(e.nodeCount+prefixSize xs)+xs.length := by omega
    rw [hf]
    rfl

theorem any_suffix {n : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n)) :
    (compileExpr b (BoolExpr.any xs)).extension.suffix=
      prefixNodes b.nodes.length xs++[BooleanNode.const false]++
        foldNodes false (b.nodes.length+prefixSize xs) (references b.nodes.length xs).reverse := by
  rw [compileExpr_nodes,any_nodes]

def items {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (value : ℕ) : List Bool→List (BoolExpr (descriptionWidth n bound))
  | []=>[]
  | bit::rest=>(if bit then unaryEqualsExpr row start limit value hblock else .const false)::
      items row start limit hblock (value+1) rest

theorem items_length {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (bits : List Bool) :
    (items row start limit hblock value bits).length=bits.length := by
  induction bits generalizing value with
  | nil=>rfl
  | cons bit bits ih=>simp only [items,List.length_cons,ih]

theorem prefix_bound {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (bits : List Bool) :
    prefixSize (items row start limit hblock value bits) ≤ bits.length*(3*limit+1) := by
  induction bits generalizing value with
  | nil=>simp only [items,prefixSize,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons bit bits ih=>
    have h:=prefixCount_bound (unaryItems row start limit value hblock)
    have hl : (unaryItems row start limit value hblock).length=limit := by simp only [unaryItems,List.length_ofFn]
    rw [hl] at h
    have ht:=ih (value+1)
    cases bit <;>
      simp only [items,Bool.false_eq_true,↓reduceIte,BoolExpr.nodeCount,prefixSize,
        List.length_cons,Nat.add_mul,Nat.one_mul,RecoveryBoundedSelectorLoop.unary_count] <;> omega

theorem saved_bound {n : ℕ} (base : ℕ) (xs : List (BoolExpr n)) (ref : ℕ)
    (hr : ref∈references base xs) : ref ≤ base+prefixSize xs := by
  induction xs generalizing base with
  | nil=>simp only [references,List.not_mem_nil] at hr
  | cons e xs ih=>
    simp only [references,List.mem_cons] at hr
    rcases hr with rfl|hr
    · simp only [prefixSize];omega
    · have h:=ih (base+e.nodeCount) hr
      simp only [prefixSize]
      omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress

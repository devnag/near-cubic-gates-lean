import Proof.Amplification.RecoveryBoundedNativeLiteral

/-! The original unary-equality grammar has a forward literal phase and
an exact reverse conjunction phase. The saved references are the original
postorder addresses, so the existing unary stack can execute that schedule. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNative
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Item (n : ℕ) := Fin n×Bool
def literal {n : ℕ} (item : Item n) : BoolExpr n :=
  if item.2 then .not (.input item.1) else .input item.1
def literalCount {n : ℕ} (item : Item n) := 1+item.2.toNat
def prefixCount {n : ℕ} : List (Item n)→ℕ
  | []=>0
  | item::rest=>literalCount item+prefixCount rest
def literalPrefix {n : ℕ} (base : ℕ) : List (Item n)→List (BooleanNode n)
  | []=>[]
  | item::rest=>exprNodes base (literal item)++literalPrefix (base+literalCount item) rest
def literalReferences {n : ℕ} (base : ℕ) : List (Item n)→List ℕ
  | []=>[]
  | item::rest=>(base+item.2.toNat)::literalReferences (base+literalCount item) rest
def allSuffix {n : ℕ} (base : ℕ) : List ℕ→List (BooleanNode n)
  | []=>[.const true]
  | ref::refs=>allSuffix base refs++[.and ref (base+refs.length)]

theorem literal_nodes {n : ℕ} (item : Item n) : (literal item).nodeCount=literalCount item := by
  rcases item with ⟨i,b⟩
  cases b <;> rfl

theorem literal_reference {n : ℕ} (base : ℕ) (item : Item n) :
    base+(literal item).nodeCount-1=base+item.2.toNat := by
  rw [literal_nodes]
  unfold literalCount
  omega

theorem references_length {n : ℕ} (base : ℕ) (items : List (Item n)) :
    (literalReferences base items).length=items.length := by
  induction items generalizing base <;> simp_all [literalReferences]

theorem all_nodeCount {n : ℕ} (items : List (Item n)) :
    (BoolExpr.all (items.map literal)).nodeCount=prefixCount items+items.length+1 := by
  induction items with
  | nil=>rfl
  | cons item rest ih=>
    simp only [List.map_cons,BoolExpr.all,BoolExpr.nodeCount,literal_nodes,ih,prefixCount,List.length_cons]
    omega

theorem all_literal_schedule {n : ℕ} (base : ℕ) (items : List (Item n)) :
    exprNodes base (BoolExpr.all (items.map literal))=
      literalPrefix base items++allSuffix (base+prefixCount items) (literalReferences base items) := by
  induction items generalizing base with
  | nil=>rfl
  | cons item rest ih=>
    simp only [List.map_cons,BoolExpr.all,exprNodes]
    rw [ih,literal_reference,all_nodeCount,literal_nodes]
    simp only [literalPrefix,literalReferences,prefixCount,allSuffix,references_length]
    have addr : base+literalCount item+(prefixCount rest+rest.length+1)-1=
        base+(literalCount item+prefixCount rest)+rest.length := by omega
    rw [addr]
    simp only [Nat.add_assoc,List.append_assoc]

def unaryItems {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit≤rowWidth n bound) : List (Item (descriptionWidth n bound)) :=
  List.ofFn fun offset : Fin limit=>
    (descriptionIndex row ⟨start+offset.val,by omega⟩,decide (¬offset.val<value))

theorem unary_expression {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit≤rowWidth n bound) :
    unaryEqualsExpr row start limit value hblock=BoolExpr.all ((unaryItems row start limit value hblock).map literal) := by
  unfold unaryEqualsExpr unaryItems
  rw [List.map_ofFn]
  congr 2
  funext offset
  by_cases h : offset.val<value <;> simp [literal,h]

theorem unary_schedule {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (hblock : start+limit≤rowWidth n bound) :
    (compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix=
      literalPrefix b.nodes.length (unaryItems row start limit value hblock)++
        allSuffix (b.nodes.length+prefixCount (unaryItems row start limit value hblock))
          (literalReferences b.nodes.length (unaryItems row start limit value hblock)) := by
  rw [compileExpr_nodes,unary_expression,all_literal_schedule]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNative

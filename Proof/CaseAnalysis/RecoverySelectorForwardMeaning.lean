import Proof.CaseAnalysis.RecoverySelectorForwardLoop

/-! The actual forward loop has the original selector's exact prefix nodes,
saved output addresses and stream cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedUniversal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldItems {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) : ℕ→List ℕ→List (BoolExpr (descriptionWidth n bound)×ℕ)
  | _,[]=>[]
  | value,ref::refs=>(unaryEqualsExpr row start limit value hblock,ref)::fieldItems row start limit hblock (value+1) refs

theorem fieldItems_length {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (value : ℕ) (refs : List ℕ) :
    (fieldItems row start limit hblock value refs).length=refs.length := by
  induction refs generalizing value <;> simp_all [fieldItems]

theorem unary_count {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) :
    (unaryEqualsExpr row start limit value hblock).nodeCount=
      prefixCount (unaryItems row start limit value hblock)+limit+1 := by
  rw [unary_expression,all_nodeCount]
  simp only [unaryItems,List.length_ofFn]

theorem next_eq {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (ref : ℕ) (a : State) :
    a.next row start limit hblock ref=
      ⟨a.position+(unaryEqualsExpr row start limit a.value hblock).nodeCount+1,a.value+1,
        a.out++(exprNodes a.position (unaryEqualsExpr row start limit a.value hblock)++
          [BooleanNode.and (a.position+(unaryEqualsExpr row start limit a.value hblock).nodeCount-1) ref]).flatMap
          PCPPRequestNodeSchema.native,
        a.skipped++frame (List.replicate ref true),
        a.stack++(frame (List.replicate (a.position+(unaryEqualsExpr row start limit a.value hblock).nodeCount) true)).reverse⟩ := by
  rw [unary_count]
  unfold State.next RecoveryBoundedSelectorReference.pushed
  have ha : a.position+(prefixCount (unaryItems row start limit a.value hblock)+limit+1)-1=
      a.position+prefixCount (unaryItems row start limit a.value hblock)+limit := by omega
  rw [ha]
  simp only [Nat.add_assoc]

theorem iterate_schedule {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (refs : List ℕ) (a : State) :
    let xs:=fieldItems row start limit hblock a.value refs
    let final:=a.iterate row start limit hblock refs
    final.position=a.position+prefixSize xs ∧
    final.value=a.value+refs.length ∧
    final.out=a.out++(prefixNodes a.position xs).flatMap PCPPRequestNodeSchema.native ∧
    final.skipped=a.skipped++sourceWord refs ∧
    final.stack=a.stack++RecoveryBoundedNativeUnaryLoop.stackWords (RecoveryBoundedUniversal.references a.position xs) := by
  induction refs generalizing a with
  | nil=>simp [fieldItems,State.iterate,prefixSize,prefixNodes,sourceWord,
      RecoveryBoundedUniversal.references,RecoveryBoundedNativeUnaryLoop.stackWords]
  | cons ref refs ih=>
    have h:=ih (a.next row start limit hblock ref)
    dsimp only at h ⊢
    rw [State.iterate]
    rw [next_eq] at h ⊢
    dsimp only at h
    rcases h with ⟨hp,hv,ho,hs,hstack⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [fieldItems,prefixSize,Nat.add_assoc] using hp
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hv
    · simpa only [fieldItems,prefixNodes,List.flatMap_append,List.append_assoc] using ho
    · simpa only [sourceWord,List.flatMap_cons,List.append_assoc] using hs
    · simpa only [fieldItems,RecoveryBoundedUniversal.references,
        RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_cons,List.append_assoc] using hstack

theorem forward_budget (count total W : ℕ) (hc : count ≤ W) (ht : total ≤ W) :
    count*(stepBudget W+2)+total+3 ≤ 134217732*(W+1)^4 := by
  have hm:=Nat.mul_le_mul_right (stepBudget W+2) hc
  unfold stepBudget at hm ⊢
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop

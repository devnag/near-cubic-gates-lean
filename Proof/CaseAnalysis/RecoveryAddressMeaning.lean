import Proof.CaseAnalysis.RecoveryAddressForward

/-! The physically emitted address prefix is the literal original plain-any
schedule, including each actual child address saved for its reverse OR fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem iterate_schedule {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (bits : List Bool) (a : State) :
    let xs:=items row start limit hblock a.value bits
    let final:=a.iterate row start limit hblock bits
    final.position=a.position+prefixSize xs ∧ final.value=a.value+bits.length ∧
    final.out=a.out++(prefixNodes a.position xs).flatMap PCPPRequestNodeSchema.native ∧
    final.skipped=a.skipped++bits ∧
    final.stack=a.stack++RecoveryBoundedNativeUnaryLoop.stackWords (references a.position xs) := by
  induction bits generalizing a with
  | nil=>simp only [items,State.iterate,prefixSize,prefixNodes,List.length_nil,Nat.add_zero,
      List.flatMap_nil,List.append_nil,references,RecoveryBoundedNativeUnaryLoop.stackWords,and_self]
  | cons bit bits ih=>
    have h:=ih (a.next row start limit hblock bit)
    dsimp only at h ⊢
    rw [State.iterate]
    dsimp only [State.next] at h ⊢
    rcases h with ⟨hp,hv,ho,hs,hstack⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [items,prefixSize,Nat.add_assoc] using hp
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hv
    · simpa only [items,prefixNodes,List.flatMap_append,List.append_assoc] using ho
    · simpa only [List.append_assoc,List.singleton_append] using hs
    · simpa only [items,references,pushed,RecoveryBoundedNativeUnaryLoop.stackWords,
        List.flatMap_cons,List.append_assoc] using hstack

theorem forward_budget (count total W : ℕ) (hc : count ≤ W) (ht : total ≤ W) :
    count*(stepBudget W+2)+total+3 ≤ 67108868*(W+1)^4 := by
  have hm:=Nat.mul_le_mul_right (stepBudget W+2) hc
  unfold stepBudget at hm ⊢
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress

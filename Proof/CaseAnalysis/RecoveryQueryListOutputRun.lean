import Proof.CaseAnalysis.RecoveryQueryListOutputBank

/-! The whole original query list returns the exact original graph and its
ordered references, with both external streams rewound for the clause/row
consumer. All scans and the actual query driver enter one fixed polynomial. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
open LocalBitMultitape RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def wholeMachine:=Composition.machine machine RecoveryBoundedQueryRewind.machine
def wholeBudget (queries W : ℕ):=budget queries W+1+(4*capacity W+5)

theorem outputs_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out tail : List Bool) (addresses : List (BitInput n)) (ht : total ≤ bound)
    (hfits : Fits b total W ht addresses) (hn : n ≤ W) (hq : addresses.length ≤ W)
    (hg : (compileUniversalOutputs b total ht addresses).final.nodes.length ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let source:=addressWord addresses++tail
    let compiled:=compileUniversalOutputs b total ht addresses
    let result:=out++native b total ht addresses
    let refs:=sourceWord (references b total ht addresses)
    ∃ r,runFrom wholeMachine (wholeBudget addresses.length W)
      ⟨wholeMachine.start,bankHeads out 0 [],bankData b.nodes.length C D F L out n total source [] addresses.length⟩=some r ∧
      r.steps ≤ wholeBudget addresses.length W ∧ r.final.heads=bankHeads result 0 [] ∧
      r.final.tapes=bankData compiled.final.nodes.length C D F L result n total source refs addresses.length := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let C:=capacity W
  let source:=addressWord addresses++tail
  let compiled:=compileUniversalOutputs b total ht addresses
  let result:=out++native b total ht addresses
  let refs:=sourceWord (references b total ht addresses)
  let H:=bankHeads result (addressWord addresses).length refs
  let A:=bankData compiled.final.nodes.length C D F L result n total source refs addresses.length
  obtain ⟨p,pr,pf,ps⟩:=queries_run b total W D L out [] tail [] addresses ht hfits hn hD hL
  simp only [List.nil_append] at pr pf
  rw [initial_config] at pr
  have ph : p.final.heads=H := by rw [pf,configuration_heads]
  have pt : p.final.tapes=A := by rw [pf,configuration_tapes]
  obtain ⟨hsource,hrefs⟩:=streams_fit b total W ht addresses hn hq hg
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedQueryRewind.both_run H A source refs C (addressWord addresses).length refs.length
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hsource hrefs
  have qr' : runFrom RecoveryBoundedQueryRewind.machine (4*C+5)
      (restart p.final RecoveryBoundedQueryRewind.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join machine RecoveryBoundedQueryRewind.machine _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,?_,qt⟩
  · change p.steps+1+q.steps ≤ wholeBudget addresses.length W
    unfold wholeBudget
    change q.steps=4*capacity W+5 at qs
    omega
  · exact qh.trans (rewound_heads result refs (addressWord addresses).length)

theorem budget_sextic (queries W : ℕ) (hq : queries ≤ W) : wholeBudget queries W ≤ 7000000000*(W+1)^6 := by
  have h:=Nat.mul_le_mul_right (RecoveryBoundedQuery.budget W+2) hq
  unfold wholeBudget budget RecoveryBoundedQuery.budget capacity
  unfold RecoveryBoundedQuery.budget at h
  nlinarith [Nat.zero_le (W^6),Nat.zero_le (W^5),Nat.zero_le (W^4),Nat.zero_le (W^3),Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueries

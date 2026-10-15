import Proof.CaseAnalysis.RecoveryRowBank

/-! The entire original query list runs on the clause consumer's bank.
The already-produced literal source and count survive at their own ports. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def queryMachine:=RecoveryFocus.machine querySlots RecoveryBoundedQueries.wholeMachine

theorem queries_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out tail pre source stack : List Bool) (clauses : ℕ)
    (addresses : List (BitInput n)) (ht : total ≤ bound)
    (hfits : RecoveryBoundedQueries.Fits b total W ht addresses) (hn : n ≤ W) (hq : addresses.length ≤ W)
    (hg : (compileUniversalOutputs b total ht addresses).final.nodes.length ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
    let C:=capacity W
    let addressSource:=RecoveryBoundedQueries.addressWord addresses++tail
    let compiled:=compileUniversalOutputs b total ht addresses
    let result:=out++RecoveryBoundedQueries.native b total ht addresses
    let refs:=sourceWord (RecoveryBoundedQueries.references b total ht addresses)
    ∃ r,runFrom queryMachine (RecoveryBoundedQueries.wholeBudget addresses.length W)
      ⟨queryMachine.start,heads out pre stack,
        data b.nodes.length C D F L out n total addressSource [] addresses.length source stack clauses⟩=some r ∧
      r.steps ≤ RecoveryBoundedQueries.wholeBudget addresses.length W ∧
      r.final.heads=heads result pre stack ∧
      r.final.tapes=data compiled.final.nodes.length C D F L result n total addressSource refs addresses.length source stack clauses := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit n bound
  let C:=capacity W
  let addressSource:=RecoveryBoundedQueries.addressWord addresses++tail
  let compiled:=compileUniversalOutputs b total ht addresses
  let result:=out++RecoveryBoundedQueries.native b total ht addresses
  let refs:=sourceWord (RecoveryBoundedQueries.references b total ht addresses)
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedQueries.outputs_run b total W D L out tail addresses ht hfits hn hq hg hD hL
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock querySlots querySlots_injective
    RecoveryBoundedQueries.wholeMachine _ (heads out pre stack)
    (data b.nodes.length C D F L out n total addressSource [] addresses.length source stack clauses)
    _ (query_heads out pre stack) (query_data _ _ _ _ _ _ _ _ _ _ _ _ _ _) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=61) (n:=12) ?_ ?_ i
    · intro j
      exact (rh j).trans ((congrFun ph j).trans (query_heads result pre stack j).symm)
    · intro j
      have hk : ∀ k,querySlots k≠j.natAdd 61 := by
        intro k he
        have hv:=congrArg (fun k : Fin 73=>k.val) he
        change k.val=61+j.val at hv
        omega
      exact (rkeep (j.natAdd 61) hk).1.trans (by simp only [heads,Fin.addCases_right])
  · funext i
    refine Fin.addCases (m:=61) (n:=12) ?_ ?_ i
    · intro j
      exact (rt j).trans ((congrFun pt j).trans (query_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ j).symm)
    · intro j
      have hk : ∀ k,querySlots k≠j.natAdd 61 := by
        intro k he
        have hv:=congrArg (fun k : Fin 73=>k.val) he
        change k.val=61+j.val at hv
        omega
      exact (rkeep (j.natAdd 61) hk).2.trans (by simp only [data,Fin.addCases_right])

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow

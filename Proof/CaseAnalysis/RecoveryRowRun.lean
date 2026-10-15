import Proof.CaseAnalysis.RecoveryRowEntry

/-! The complete original verifier row. Both original workers run in one
bank, with the actual source and finite drivers retained during the join. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape Composition SourceInterfaces RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Calls
variable {a b : ℕ} (first : Machine 73 a) (second : Machine 73 b)
def machine:=Composition.machine first second
theorem join (H : Fin 73→ℕ) (A : Fin 73→List Bool) (u v : ℕ)
    (p : ExecutionReceipt 73 a) (q : ExecutionReceipt 73 b)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom second v (restart p.final second.start)=some q) :
    ∃ r,runFrom (machine first second) (u+1+v) ⟨(machine first second).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join first second _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Calls

noncomputable def machine:=Calls.machine queryMachine RecoveryBoundedClauses.machine
def budget (queries clauses W : ℕ):=
  RecoveryBoundedQueries.wholeBudget queries W+1+RecoveryBoundedClauses.budget clauses W (capacity W)

theorem row_run {sourceMachine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
    (pcp : ProjectionPCP sourceMachine timeBound) {n bound : ℕ} (input : BitInput n)
    (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hc : count ≤ bound) (randomness : BitInput (pcp.nativeWidth n))
    (W D L : ℕ) (out addressTail pre tail stack : List Bool)
    (hfits : RecoveryBoundedQueries.Fits b count W hc (projectedAddresses pcp input randomness))
    (hn : pcp.nativeWidth n ≤ W) (hq : pcp.queryCount n ≤ W)
    (hFinal : (compileVerifierRow pcp input b count hc randomness).compiled.final.nodes.length ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L)
    (hLC : capacity W+5*W+7 ≤ L) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit (pcp.nativeWidth n) bound
    let C:=capacity W
    let addresses:=projectedAddresses pcp input randomness
    let clauses:=(pcp.decision input randomness).clauses
    let addressSource:=RecoveryBoundedQueries.addressWord addresses++addressTail
    let source:=pre++RecoveryBoundedClauseList.word clauses++tail
    let compiled:=compileVerifierRow pcp input b count hc randomness
    ∃ right erased r,runFrom machine (budget (pcp.queryCount n) clauses.length W)
      ⟨machine.start,heads out pre stack,
        data b.nodes.length C D F L out (pcp.nativeWidth n) count addressSource [] (pcp.queryCount n) source stack clauses.length⟩=some r ∧
      r.steps ≤ budget (pcp.queryCount n) clauses.length W ∧ right ≤ W ∧ erased ≤ C ∧
      RecoveryBoundedClauseState.State (r.final.heads∘clauseSlots) (r.final.tapes∘clauseSlots)
        compiled.compiled.final.nodes.length compiled.compiled.output.val right C L
        (out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)
        (pre++RecoveryBoundedClauseList.word clauses) source
        (sourceWord (RecoveryBoundedQueries.references b count hc addresses)) ∧
      r.final.heads 71=stack.length ∧ r.final.tapes 71=stack++List.replicate erased false ∧
      r.final.heads 72=1 ∧ r.final.tapes 72=CompareMachine.word clauses.length := by
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit (pcp.nativeWidth n) bound
  let C:=capacity W
  let addresses:=projectedAddresses pcp input randomness
  let clauses:=(pcp.decision input randomness).clauses
  let addressSource:=RecoveryBoundedQueries.addressWord addresses++addressTail
  let source:=pre++RecoveryBoundedClauseList.word clauses++tail
  let queried:=rowQueries pcp input b count hc randomness
  let queryOut:=out++RecoveryBoundedQueries.native b count hc addresses
  let refs:=sourceWord (RecoveryBoundedQueries.references b count hc addresses)
  let H:=heads queryOut pre stack
  let A:=data queried.final.nodes.length C D F L queryOut (pcp.nativeWidth n) count addressSource refs (pcp.queryCount n)
    source stack clauses.length
  have hlen : addresses.length=pcp.queryCount n:=projectedAddresses_length pcp input randomness
  have hquery := query_bound pcp input b count hc randomness W hFinal
  obtain ⟨p,pr,ps,ph,pt⟩:=queries_run b count W D L out addressTail pre source stack clauses.length addresses hc hfits hn
    (by rw [hlen];exact hq) hquery hD hL
  rw [hlen] at pr ps pt
  have state : RecoveryBoundedClauseState.State ((H∘bodySlots)∘RecoveryBoundedClauseCollect.old)
      ((A∘bodySlots)∘RecoveryBoundedClauseCollect.old) queried.final.nodes.length 0 0 C L queryOut pre source
      (sourceWord (RecoveryBoundedLiteral.references queried.values)) := by
    rw [body_clause,body_clause_data,references_eq]
    exact clause_state queried.final.nodes.length C D F L queryOut pre (pcp.nativeWidth n) count
      addressSource refs (pcp.queryCount n) source stack clauses.length
  obtain ⟨right,erased,q,qr,qs,qright,qerased,qstate,qSH,qSA,qDH,qDA⟩:=RecoveryBoundedClauses.clauses_run
    queried.final queried.values (query_length pcp input b count hc randomness) clauses (H∘bodySlots) (A∘bodySlots)
    0 0 W C L queryOut pre source tail stack state rfl rfl rfl hFinal hq (Nat.zero_le W) (Nat.zero_le W) (by rfl) hLC
  rw [clause_entry H A clauses.length rfl rfl] at qr
  have qr' : runFrom RecoveryBoundedClauses.machine (RecoveryBoundedClauses.budget clauses.length W C)
      (restart p.final RecoveryBoundedClauses.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  obtain ⟨r,rr,rs,rh,rt⟩:=Calls.join queryMachine RecoveryBoundedClauses.machine
    (heads out pre stack)
    (data b.nodes.length C D F L out (pcp.nativeWidth n) count addressSource [] (pcp.queryCount n) source stack clauses.length)
    (RecoveryBoundedQueries.wholeBudget (pcp.queryCount n) W) (RecoveryBoundedClauses.budget clauses.length W C) p q pr qr'
  refine ⟨right,erased,r,rr,?_,qright,qerased,?_,?_,?_,?_,?_⟩
  · rw [rs]
    exact Nat.add_le_add (Nat.add_le_add_right ps 1) qs
  · rw [rh,rt,original_native,original_output,original_final,List.append_assoc]
    rw [references_eq] at qstate
    have hslots : RecoveryBoundedClauseFold.old=clauseSlots:=rfl
    rw [hslots] at qstate
    simpa only [queryOut,source,List.append_assoc,queried,clauses,C,addresses,rowDecision] using qstate
  · rw [rh];exact qSH
  · rw [rt];exact qSA
  · rw [rh];exact qDH
  · rw [rt];exact qDA

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow

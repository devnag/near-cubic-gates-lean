import Proof.CaseAnalysis.RecoveryClauseResult

/-! The complete original compileClauses consumer, including its paid
forward driver, reverse ANDs, final live reference and actual graph count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauses
open LocalBitMultitape Composition SourceInterfaces RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedClauseCollect (old)
open RecoveryBoundedLiteral (references)
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Calls
variable {a b c : ℕ} (first : Machine 73 a) (second : Machine 73 b) (last : Machine 73 c)
def prepare:=Composition.machine first second
def machine:=Composition.machine (prepare first second) last
theorem joined (H : Fin 73→ℕ) (A : Fin 73→List Bool) (u v w : ℕ)
    (p : ExecutionReceipt 73 a) (q : ExecutionReceipt 73 b) (r : ExecutionReceipt 73 c)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom second v (restart p.final second.start)=some q)
    (hr : runFrom last w (restart q.final last.start)=some r) :
    ∃ s,runFrom (machine first second last) (u+1+v+1+w) ⟨(machine first second last).start,H,A⟩=some s ∧
      s.steps=p.steps+1+q.steps+1+r.steps ∧ s.final.heads=r.final.heads ∧ s.final.tapes=r.final.tapes := by
  have pq:=Composition.run_join first second _ _ _ p q hp hq
  have full:=Composition.run_join (prepare first second) last _ _ _ (joinedReceipt p q) r pq hr
  exact ⟨joinedReceipt (joinedReceipt p q) r,full,rfl,rfl,rfl⟩
end Calls

noncomputable def machine:=Calls.machine RecoveryBoundedClauseList.forwardMachine RecoveryBoundedClauseFold.machine
  RecoveryBoundedClauseResult.machine
def forwardBudget (count W C : ℕ):=count*(RecoveryBoundedClauseBody.budget W C+2)+count+3
def budget (count W C : ℕ):=forwardBudget count W C+1+RecoveryBoundedClauseFold.budget count C+1+(2*C+4*W+14)
noncomputable def entry (H : Fin 72→ℕ) (A : Fin 72→List Bool) (count : ℕ):=
  restart (RecoveryBoundedClauseList.configuration 0 H A count 1) machine.start

theorem configuration_heads (phase : Fin 5) (H : Fin 72→ℕ) (A : Fin 72→List Bool) (total driver : ℕ) :
    (RecoveryBoundedClauseList.configuration phase H A total driver).heads∘RecoveryBoundedClauseFold.old=H∘old := by
  funext j
  change Fin.addCases H (fun _ : Fin 1=>driver) ((old j).castAdd 1)=H (old j)
  simp only [Fin.addCases_left]
theorem configuration_data (phase : Fin 5) (H : Fin 72→ℕ) (A : Fin 72→List Bool) (total driver : ℕ) :
    (RecoveryBoundedClauseList.configuration phase H A total driver).tapes∘RecoveryBoundedClauseFold.old=A∘old := by
  funext j
  change Fin.addCases A (fun _ : Fin 1=>CompareMachine.word total) ((old j).castAdd 1)=A (old j)
  simp only [Fin.addCases_left]

theorem clauses_run {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clauses : List (Fin 3→Literal q)) (H : Fin 72→ℕ) (A : Fin 72→List Bool) (left right W C L : ℕ)
    (out pre source tail stack : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) b.nodes.length left right C L out pre source (sourceWord (references values)))
    (hSH : H 71=stack.length) (hSA : A 71=stack)
    (hSource : source=pre++RecoveryBoundedClauseList.word clauses++tail)
    (hFinal : (compileClauses b values hv clauses).final.nodes.length ≤ W)
    (hq : q ≤ W) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (hL : C+5*W+7 ≤ L) :
    let compiled:=compileClauses b values hv clauses
    ∃ finalRight erased r,runFrom machine (budget clauses.length W C) (entry H A clauses.length)=some r ∧
      r.steps ≤ budget clauses.length W C ∧ finalRight ≤ W ∧ erased ≤ C ∧
      RecoveryBoundedClauseState.State (r.final.heads∘RecoveryBoundedClauseFold.old) (r.final.tapes∘RecoveryBoundedClauseFold.old)
        compiled.final.nodes.length compiled.output.val finalRight C L
        (out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native) (pre++RecoveryBoundedClauseList.word clauses)
        source (sourceWord (references values)) ∧
      r.final.heads 71=stack.length ∧ r.final.tapes 71=stack++List.replicate erased false ∧
      r.final.heads 72=1 ∧ r.final.tapes 72=CompareMachine.word clauses.length := by
  let compiled:=compileClauses b values hv clauses
  obtain ⟨f,p,pr,pf,ps⟩:=RecoveryBoundedClauseList.forward_run b values hv clauses W C L clauses.length 0 H A left right
    out pre source tail stack h hSH hSA hSource (by omega) hFinal hq hl hr hC hL
  let nextOut:=out++f.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let nextPre:=pre++RecoveryBoundedClauseList.word clauses
  have state : RecoveryBoundedClauseState.State (p.final.heads∘RecoveryBoundedClauseFold.old)
      (p.final.tapes∘RecoveryBoundedClauseFold.old) f.next.nodes.length f.left f.right C L nextOut nextPre source
      (sourceWord (references values)) := by
    rw [pf,configuration_heads,configuration_data]
    exact f.state
  have pSH : p.final.heads 71=(stack++RecoveryBoundedClauseList.stackWord f.refs).length := by rw [pf];exact f.stackH
  have pSA : p.final.tapes 71=stack++RecoveryBoundedClauseList.stackWord f.refs := by rw [pf];exact f.stackA
  have pDH : p.final.heads 72=1:=by rw [pf];rfl
  have pDA : p.final.tapes 72=CompareMachine.word f.refs.length:=by rw [pf,f.refs_length];rfl
  have hcount : compiled.final.nodes.length=f.next.nodes.length+f.refs.length+1 := by
    rw [f.nodes,List.length_append,RecoveryBoundedClauseList.allSuffix_length]
    omega
  have hFinal' : compiled.final.nodes.length ≤ W:=hFinal
  have ha : f.next.nodes.length+f.refs.length ≤ W:=by omega
  obtain ⟨q,qr,qs,qh,qt,qkeep⟩:=RecoveryBoundedClauseFold.fold_run p.final.heads p.final.tapes f.next.nodes.length f.left f.right
    W C L nextOut nextPre source (sourceWord (references values)) stack f.refs state pSH pSA pDH pDA f.refs_bound ha
    f.left_bound f.right_bound hC
  let folded:=RecoveryBoundedClauseFold.finalState f.next.nodes.length (nextOut++RecoveryBoundedNativeUnaryPhase.trueBits) f.refs
  have hc : 1 ≤ C:=by nlinarith [Nat.zero_le (W^2)]
  have qstate:=RecoveryBoundedClauseFold.fold_state p.final.heads q.final.heads p.final.tapes q.final.tapes
    f.next.nodes.length f.left f.right C L f.refs.length nextOut nextPre source (sourceWord (references values)) stack f.refs
    state qh qt qkeep hc
  have hm:=RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=n) true f.refs.reverse
    ⟨f.next.nodes.length,0,0,nextOut++RecoveryBoundedNativeUnaryPhase.trueBits⟩
  have hacc : folded.acc=f.next.nodes.length+f.refs.length := by
    simpa only [folded,RecoveryBoundedClauseFold.finalState,List.length_reverse] using hm.1
  have hgraph : folded.out=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native := by
    rw [show folded.out=(nextOut++RecoveryBoundedNativeUnaryPhase.trueBits)++
        (foldNodes (n:=n) true f.next.nodes.length f.refs.reverse).flatMap PCPPRequestNodeSchema.native from hm.2]
    rw [RecoveryBoundedClauseList.suffix_eq f.extension compiled.extension f.refs f.nodes,allSuffix_reverse]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,nextOut,List.append_assoc]
    rfl
  have haccW : folded.acc ≤ W:=hacc ▸ ha
  obtain ⟨r,rr,rs,rh,rt,rstate⟩:=RecoveryBoundedClauseResult.result_run q.final.heads q.final.tapes folded.acc f.right W C L
    folded.out nextPre source (sourceWord (references values)) qstate haccW hC
  obtain ⟨result,resultRun,resultSteps,resultHeads,resultTapes⟩:=Calls.joined RecoveryBoundedClauseList.forwardMachine
    RecoveryBoundedClauseFold.machine RecoveryBoundedClauseResult.machine
    (RecoveryBoundedClauseList.configuration 0 H A clauses.length 1).heads
    (RecoveryBoundedClauseList.configuration 0 H A clauses.length 1).tapes
    (forwardBudget clauses.length W C) (RecoveryBoundedClauseFold.budget f.refs.length C)
    (RecoveryBoundedClauseReplace.budget folded.acc C) p q r pr qr rr
  have hreplace : RecoveryBoundedClauseReplace.budget folded.acc C ≤ 2*C+4*W+14 := by
    unfold RecoveryBoundedClauseReplace.budget
    omega
  rw [f.refs_length] at resultRun qs
  have hb : forwardBudget clauses.length W C+1+RecoveryBoundedClauseFold.budget clauses.length C+1+
      RecoveryBoundedClauseReplace.budget folded.acc C ≤ budget clauses.length W C := by unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget clauses.length W C-
    (forwardBudget clauses.length W C+1+RecoveryBoundedClauseFold.budget clauses.length C+1+
      RecoveryBoundedClauseReplace.budget folded.acc C)) _ result resultRun
  rw [Nat.add_sub_of_le hb] at more
  have hz0:=RecoveryBoundedSelectorLoop.erased_bound true W f.refs.reverse
    ⟨f.next.nodes.length,0,0,nextOut++RecoveryBoundedNativeUnaryPhase.trueBits⟩
    (by intro ref href;exact f.refs_bound ref (List.mem_reverse.mp href))
  have hz : folded.erased ≤ C := by
    change folded.erased ≤ 0+f.refs.reverse.length*(2*W+1) at hz0
    rw [List.length_reverse,Nat.zero_add] at hz0
    have hlen : f.refs.length ≤ W:=by omega
    have hm:=Nat.mul_le_mul_right (2*W+1) hlen
    nlinarith [Nat.zero_le (W^2)]
  refine ⟨f.right,folded.erased,result,more,?_,f.right_bound,hz,?_,?_,?_,?_,?_⟩
  · rw [resultSteps]
    unfold budget forwardBudget
    rw [rs]
    omega
  · rw [resultHeads,resultTapes]
    rw [f.output,hcount,←hacc,←hgraph]
    exact rstate
  · rw [resultHeads,rh]
    have hh:=qh 31
    rw [RecoveryBoundedClauseFold.output_heads] at hh
    exact hh
  · rw [resultTapes,rt]
    change q.final.tapes 71=stack++List.replicate folded.erased false
    have ht:=qt 31
    rw [RecoveryBoundedClauseFold.output_data _ _ _ _ _ _ hc] at ht
    exact ht
  · rw [resultHeads,rh]
    have hh:=qh 34
    rw [RecoveryBoundedClauseFold.output_heads] at hh
    exact hh
  · rw [resultTapes,rt]
    change q.final.tapes 72=CompareMachine.word clauses.length
    have ht:=qt 34
    rw [RecoveryBoundedClauseFold.output_data _ _ _ _ _ _ hc,f.refs_length] at ht
    exact ht

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauses

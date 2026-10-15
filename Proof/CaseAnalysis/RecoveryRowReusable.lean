import Proof.CaseAnalysis.RecoveryRowResetBank
import Proof.MachineModel.OrdinaryMatrixBucketRootPower

/-! The complete original verifier row, its saved result, and its paid
reusable bank. The next original row only needs its freshly produced addresses. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReusable
open LocalBitMultitape Composition SourceInterfaces RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Calls
variable {a b : ℕ} (first : Machine 78 a) (second : Machine 78 b)
def machine:=Composition.machine first second
theorem join (H : Fin 78→ℕ) (A : Fin 78→List Bool) (u v : ℕ)
    (p : ExecutionReceipt 78 a) (q : ExecutionReceipt 78 b)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom second v (restart p.final second.start)=some q) :
    ∃ r,runFrom (machine first second) (u+1+v) ⟨(machine first second).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join first second _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Calls

noncomputable def machine:=Calls.machine first RecoveryBoundedRowAfter.machine
def budget (u ref B : ℕ) (fields : Fin 78→List Bool):=2*(u+2)+2+1+RecoveryBoundedRowAfter.budget ref B fields

theorem state_fields (H : Fin 73→ℕ) (A : Fin 73→List Bool) (node ref right C L : ℕ)
    (out pre source refs : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘RecoveryBoundedRow.clauseSlots) (A∘RecoveryBoundedRow.clauseSlots)
      node ref right C L out pre source refs) :
    H 20=out.length ∧ A 20=out ∧ A 25=List.replicate node true ∧
      A 45=ZeroPadding.pad C (List.replicate ref true) ∧ A 70=source := by
  refine ⟨h.gateH 20,?_,h.restoreA 0,h.restoreA 1,h.sourceA⟩
  have ha:=h.gateA 20
  change A 20=ZeroPadding.pad 0 out at ha
  simpa only [ZeroPadding.pad_zero] using ha

theorem row_run {sourceMachine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
    (pcp : ProjectionPCP sourceMachine timeBound) {n bound : ℕ} (input : BitInput n)
    (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hc : count≤bound) (randomness : BitInput (pcp.nativeWidth n))
    (W D L B S : ℕ) (out addressTail sourceTail stack packetTail : List Bool)
    (hfits : RecoveryBoundedQueries.Fits b count W hc (projectedAddresses pcp input randomness))
    (hn : pcp.nativeWidth n≤W) (hq : pcp.queryCount n≤W)
    (hFinal : (compileVerifierRow pcp input b count hc randomness).compiled.final.nodes.length≤W)
    (hD : 8388608*(W+1)^3≤D) (hL : RecoveryBoundedSelectorFinish.logCapacity W≤L)
    (hLC : capacity W+5*W+7≤L) (hCB : capacity W+1≤B) (hDB : D≤B) (hLB : L≤B)
    (hS : 1≤S) (ho : out.length≤S) :
    let C:=capacity W
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit (pcp.nativeWidth n) bound
    let clauses:=(pcp.decision input randomness).clauses
    let source:=RecoveryBoundedClauseList.word clauses++sourceTail
    let u:=RecoveryBoundedRow.budget (pcp.queryCount n) clauses.length W
    let f:=RecoveryBoundedRowPrototype.fields C D F L (pcp.nativeWidth n) count (pcp.queryCount n) clauses.length
    let packet:=RecoveryBoundedRowReload.word f++packetTail
    let A:=RecoveryBoundedRow.data b.nodes.length C D F L out (pcp.nativeWidth n) count
      (RecoveryBoundedQueries.addressWord (projectedAddresses pcp input randomness)++addressTail) [] (pcp.queryCount n) source [] clauses.length
    let compiled:=compileVerifierRow pcp input b count hc randomness
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let nextStack:=RecoveryBoundedClauseCollect.pushed compiled.compiled.output.val stack
    let nextA:=RecoveryBoundedRow.data compiled.compiled.final.nodes.length C D F L result (pcp.nativeWidth n) count
      [] [] (pcp.queryCount n) source [] clauses.length
    (∀ i,(A i).length≤S) → S+u+3≤B →
    (∀ j∈RecoveryBoundedRowReload.ports,(f j).length≤B) → (RecoveryBoundedRowReload.word f).length≤B →
    ∃ r,runFrom machine (budget u compiled.compiled.output.val B f)
      ⟨machine.start,RecoveryBoundedRowAfter.heads out stack,
        RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B A) B stack packet⟩=some r ∧
      r.steps≤budget u compiled.compiled.output.val B f ∧
      r.final.heads=RecoveryBoundedRowAfter.heads result nextStack ∧
      r.final.tapes=RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B nextA) B nextStack packet := by
  let C:=capacity W
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit (pcp.nativeWidth n) bound
  let clauses:=(pcp.decision input randomness).clauses
  let source:=RecoveryBoundedClauseList.word clauses++sourceTail
  let u:=RecoveryBoundedRow.budget (pcp.queryCount n) clauses.length W
  let f:=RecoveryBoundedRowPrototype.fields C D F L (pcp.nativeWidth n) count (pcp.queryCount n) clauses.length
  let packet:=RecoveryBoundedRowReload.word f++packetTail
  let A:=RecoveryBoundedRow.data b.nodes.length C D F L out (pcp.nativeWidth n) count
    (RecoveryBoundedQueries.addressWord (projectedAddresses pcp input randomness)++addressTail) [] (pcp.queryCount n) source [] clauses.length
  let compiled:=compileVerifierRow pcp input b count hc randomness
  let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  dsimp only
  intro hA hB hf hw
  obtain ⟨right,erased,r,rr,rs,_,_,state,_,_,_,_⟩:=RecoveryBoundedRow.row_run pcp input b count hc randomness
    W D L out addressTail [] sourceTail [] hfits hn hq hFinal hD hL hLC
  have sourceRun : runFrom RecoveryBoundedRow.machine u
      ⟨RecoveryBoundedRow.machine.start,RecoveryBoundedRow.heads out [] [],A⟩=some r := by
    simpa only [A,u,source,List.nil_append] using rr
  obtain ⟨h20,a20,a25,a45,a70⟩:=state_fields r.final.heads r.final.tapes _ _ right C L
    result (RecoveryBoundedClauseList.word clauses) source
    (sourceWord (RecoveryBoundedQueries.references b count hc (projectedAddresses pcp input randomness))) state
  obtain ⟨p,pr,ps,ph,pt,pb⟩:=reset_bank_run out result stack packet A u S B r sourceRun rs hS ho hA hB h20
  have href : 2*compiled.compiled.output.val+2≤B := by
    have hr:=compiled.compiled.output.isLt
    have hB' : capacity W≤B:=by omega
    unfold capacity at hB'
    nlinarith [Nat.zero_le (W^2)]
  have p20 : RecoveryBoundedRowReuse.paddedData B r.final.tapes 20=result := by
    change ZeroPadding.pad 0 (r.final.tapes 20)=result
    rw [ZeroPadding.pad_zero]
    exact a20
  have p25 : RecoveryBoundedRowReuse.paddedData B r.final.tapes 25=List.replicate compiled.compiled.final.nodes.length true := by
    change ZeroPadding.pad 0 (r.final.tapes 25)=_
    rw [ZeroPadding.pad_zero]
    exact a25
  have p70 : RecoveryBoundedRowReuse.paddedData B r.final.tapes 70=source := by
    change ZeroPadding.pad 0 (r.final.tapes 70)=source
    rw [ZeroPadding.pad_zero]
    exact a70
  have p45 : RecoveryBoundedRowReuse.paddedData B r.final.tapes 45=ZeroPadding.pad B (List.replicate compiled.compiled.output.val true) := by
    change ZeroPadding.pad B (r.final.tapes 45)=_
    rw [a45]
    exact MatrixBucketRootPower.pad_pad C B _ (by omega)
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedRowAfter.after_run compiled.compiled.final.nodes.length compiled.compiled.output.val
    C D F L (pcp.nativeWidth n) count (pcp.queryCount n) clauses.length B result source stack packetTail
    (RecoveryBoundedRowReuse.paddedData B r.final.tapes) pb p20 p25 p70 p45 hCB hDB hLB href hf hw
  have qr' : runFrom RecoveryBoundedRowAfter.machine (RecoveryBoundedRowAfter.budget compiled.compiled.output.val B f)
      (restart p.final RecoveryBoundedRowAfter.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  obtain ⟨whole,wr,ws,wh,wt⟩:=Calls.join first RecoveryBoundedRowAfter.machine
    (RecoveryBoundedRowAfter.heads out stack) (RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B A) B stack packet)
    (2*(u+2)+2) (RecoveryBoundedRowAfter.budget compiled.compiled.output.val B f) p q pr qr'
  refine ⟨whole,wr,?_,wh.trans qh,wt.trans qt⟩
  rw [ws]
  exact Nat.add_le_add (Nat.add_le_add_right ps 1) qs

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReusable

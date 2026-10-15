import Proof.CaseAnalysis.RecoveryFixedRowsAfter

/-! Whole original verifier rows and the original final AND, followed by
the paid saved-output, bank and projector continuation for the next count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Reuse
variable {s : ℕ}
noncomputable def first (worker : Machine 116 s):=Whole.machine worker RecoveryBoundedFixedContinue.machine
noncomputable def machine (worker : Machine 116 s):=Whole.machine (first worker) RecoveryBoundedFixedRestart.machine
def budget (u B R : ℕ):=u+1+64*(B+2)+1+(4*R+6)

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem join (worker : Machine 116 s) (u : ℕ) (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (P : ℕ)
    (f : Forward z (compileExpr b (fixedCountGrammarExpr (n:=R) count)).final (allRandomness R))
    (a : ExecutionReceipt 116 s)
    (ar : runFrom worker u ⟨worker.start,H,A⟩=some a) (as : a.steps≤u)
    (ah : a.final.heads=(result z f.next f.refs (compileExpr b (fixedCountGrammarExpr (n:=R) count)).output.val stack).heads)
    (aT : a.final.tapes=stackPadded P
      (result z f.next f.refs (compileExpr b (fixedCountGrammarExpr (n:=R) count)).output.val stack).tapes)
    (ag : a.final.tapes 20=z.word (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final)
    (ao : a.final.tapes 25=List.replicate
      (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).output.val true)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G)
    (hP : stack.length+(2^R+1)*(2*z.W+1)≤P) :
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    ∃ r,runFrom (machine worker) (budget u z.B R) ⟨(machine worker).start,H,A⟩=some r ∧
      r.steps≤budget u z.B R ∧
      r.final.heads=RecoveryBoundedFixedRestart.nextHeads (z.word original.final) saved ∧
      r.final.tapes=RecoveryBoundedFixedRestart.data P (z.rowBank original.final saved)
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B) (2^R) := by
  let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
  let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
  let saved:=RecoveryBoundedAddress.pushed original.output.val stack
  have hGraph : (result z f.next f.refs grammar.output.val stack).tapes 20=z.word original.final := by
    rw [aT] at ag
    change ZeroPadding.pad 0 ((result z f.next f.refs grammar.output.val stack).tapes 20)=_ at ag
    simpa only [ZeroPadding.pad_zero] using ag
  have hOutput : f.next.nodes.length+f.refs.length+1=original.output.val := by
    rw [aT] at ao
    change ZeroPadding.pad 0 ((result z f.next f.refs grammar.output.val stack).tapes 25)=_ at ao
    rw [ZeroPadding.pad_zero,result,RecoveryBoundedCountConjunction.result_output] at ao
    simpa only [List.length_replicate] using congrArg List.length ao
  obtain ⟨q,qr,qs,qh,qt⟩:=save_run z b stack P f hFinal hGraph hOutput hP
  have qr' : runFrom RecoveryBoundedFixedContinue.machine (64*(z.B+2))
      (restart a.final RecoveryBoundedFixedContinue.machine.start)=some q := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some q
    rw [ah,aT]
    exact qr
  obtain ⟨joined,jr,js,jh,jt⟩:=Whole.join worker RecoveryBoundedFixedContinue.machine H A u (64*(z.B+2)) a q ar qr'
  obtain ⟨last,lr,ls,lh,lt⟩:=RecoveryBoundedFixedRestart.run p R Q (2^R-1) z.B P (2^R)
    (z.word original.final) saved (z.rowBank original.final saved)
  have lr' : runFrom RecoveryBoundedFixedRestart.machine (4*R+6)
      (restart joined.final RecoveryBoundedFixedRestart.machine.start)=some last := by
    change runFrom _ _ ⟨_,joined.final.heads,joined.final.tapes⟩=some last
    rw [jh,jt,qh,qt]
    exact lr
  obtain ⟨r,rr,rs,rh,rt⟩:=Whole.join (first worker) RecoveryBoundedFixedRestart.machine H A
    (u+1+64*(z.B+2)) (4*R+6) joined last jr lr'
  refine ⟨r,rr,?_,rh.trans lh,rt.trans lt⟩
  rw [rs,js]
  unfold budget
  omega
end Reuse

noncomputable def reusableMachine:=Reuse.machine machine
def reusableBudget (B W R : ℕ):=Reuse.budget (budget B W R) B R

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem reusable_run (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (P : ℕ)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G)
    (hP : stack.length+(2^R+1)*(2*z.W+1)≤P) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    ∃ r,runFrom reusableMachine (reusableBudget z.B z.W R)
      ⟨reusableMachine.start,startHeads (z.heads grammar.final (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)),
        stackPadded P (scanData (z.bank grammar.final 0 (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)) (2^R))⟩=some r ∧
      r.steps≤reusableBudget z.B z.W R ∧
      r.final.heads=RecoveryBoundedFixedRestart.nextHeads (z.word original.final) saved ∧
      r.final.tapes=RecoveryBoundedFixedRestart.data P (z.rowBank original.final saved)
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B) (2^R) := by
  obtain ⟨f,a,ar,as,ah,aT,ag,ao⟩:=padded_run z P b stack hFinal
  exact Reuse.join machine (budget z.B z.W R) _ _ z b stack P f a ar as ah aT ag ao hFinal hP

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows

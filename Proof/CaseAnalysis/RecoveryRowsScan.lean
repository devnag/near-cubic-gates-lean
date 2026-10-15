import Proof.CaseAnalysis.RecoveryRowsForward

/-! The terminal original row follows the paid finite driver. This covers
width zero and preserves the exact reference order for the original ANDs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Spine.tail_bound {m : TimedDecisionMachine} {t : ℕ→ℕ} {pcp : ProjectionPCP m t}
    {n bound : ℕ} {x : BitInput n} {count : ℕ} {hc : count≤bound} {b c rows refs}
    (h : Spine pcp x count hc b rows c refs) (rest : List (BitInput (pcp.nativeWidth n))) (G : ℕ)
    (hg : (compileVerifierRows pcp x count hc b (rows++rest)).final.nodes.length≤G) :
    (compileVerifierRows pcp x count hc c rest).final.nodes.length≤G := by
  induction h with
  | nil=>exact hg
  | cons b r rows next refs h ih=>exact ih (RecoveryBoundedRows.tail_bound pcp x count hc b r (rows++rest) G hg)

def scanHeads (H : Fin 115→ℕ) : Fin 116→ℕ:=Fin.addCases (m:=115) (n:=1) (motive:=fun _=>ℕ) H (fun _=>1)
def startHeads (H : Fin 115→ℕ) : Fin 116→ℕ:=Fin.addCases (m:=115) (n:=1) (motive:=fun _=>ℕ) H (fun _=>2)
def scanData (A : Fin 115→List Bool) (total : ℕ) : Fin 116→List Bool:=
  Fin.addCases (m:=115) (n:=1) (motive:=fun _=>List Bool) A (fun _=>CompareMachine.word total)

namespace Tail
variable {a b : ℕ}
def last (worker : Machine 115 b):=TapeEmbedding.machine 1 worker
def machine (first : Machine 116 a) (worker : Machine 115 b):=Composition.machine first (last worker)
theorem run (worker : Machine 115 b) (H : Fin 115→ℕ) (A : Fin 115→List Bool) (total u : ℕ)
    (base : ExecutionReceipt 115 b) (hr : runFrom worker u ⟨worker.start,H,A⟩=some base) :
    ∃ r,runFrom (last worker) u ⟨(last worker).start,scanHeads H,scanData A total⟩=some r ∧
      r.steps=base.steps ∧ r.final.heads=scanHeads base.final.heads ∧ r.final.tapes=scanData base.final.tapes total := by
  exact ⟨TapeEmbedding.receipt (fun _=>1) (fun _=>CompareMachine.word total) base,
    TapeEmbedding.run_embed worker (fun _=>1) (fun _=>CompareMachine.word total) _ _ base hr,rfl,rfl,rfl⟩
theorem join (first : Machine 116 a) (worker : Machine 115 b) (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (u v : ℕ) (p : ExecutionReceipt 116 a) (q : ExecutionReceipt 116 b)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom (last worker) v (restart p.final (last worker).start)=some q) :
    ∃ r,runFrom (machine first worker) (u+1+v) ⟨(machine first worker).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join first (last worker) _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Tail

def scanBudget (B total : ℕ):=total*(bodyBudget B+2)+(total+1)+3+1+finishBudget B

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : ℕ} {hc : count≤bound}

namespace Scan
variable {s t : ℕ}
noncomputable def machine (worker : Machine 115 s) (terminal : Machine 115 t):=Tail.machine (Driver.machine worker) terminal

theorem scan_run (worker : Machine 115 s) (terminal : Machine 115 t) (z : Resources p R Q hr hq x count hc)
    (bodySupplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool), k+1<2^R →
      (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)).compiled.final.nodes.length≤z.G →
      let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
      let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
      ∃ r,runFrom worker (bodyBudget z.B) ⟨worker.start,z.heads b stack,z.bank b k stack⟩=some r ∧
        r.steps≤bodyBudget z.B ∧ r.final.heads=z.heads row.compiled.final saved ∧
        r.final.tapes=z.bank row.compiled.final (k+1) saved)
    (lastSupplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool),
      (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)).compiled.final.nodes.length≤z.G →
      let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
      let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
      ∃ r,runFrom terminal (finishBudget z.B) ⟨terminal.start,z.heads b stack,z.bank b k stack⟩=some r ∧
        r.steps≤finishBudget z.B ∧ r.final.heads=z.heads row.compiled.final saved ∧
        r.final.tapes=z.bank row.compiled.final k saved)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (total : ℕ) (stack : List Bool) (hk : total<2^R)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R 0 (total+1))).final.nodes.length≤z.G) :
    ∃ f : Forward z b (randomnesses R 0 (total+1)), ∃ r,
      runFrom (machine worker terminal) (scanBudget z.B total)
        ⟨(machine worker terminal).start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (total+1)⟩=some r ∧
      r.steps≤ scanBudget z.B total ∧
      r.final.heads=scanHeads (z.heads f.next (stack++stackWord f.refs)) ∧
      r.final.tapes=scanData (z.bank f.next total (stack++stackWord f.refs)) (total+1) := by
  have hall : randomnesses R 0 (total+1)=randomnesses R 0 total++[bitInputOfCode R total] := by
    simpa only [Nat.zero_add] using randomnesses_append R 0 total
  have hg:=hFinal
  rw [hall] at hg
  obtain ⟨f,a,ar,af,as⟩:=Driver.forward_run worker z bodySupplier b total 0 [bitInputOfCode R total] stack (total+1) 1 (by omega) (by simpa using hk) hg
  simp only [Nat.zero_add] at af
  let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x f.next count hc (bitInputOfCode R total)
  have hrow : row.compiled.final.nodes.length≤z.G:=head_bound (compactProjectionPCP (p.normalized R Q hr hq))
    x count hc f.next (bitInputOfCode R total) [] z.G (f.spine.tail_bound _ _ hg)
  let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val (stack++stackWord f.refs)
  obtain ⟨base,br,bs,bh,bt⟩:=lastSupplier f.next total (stack++stackWord f.refs) hrow
  obtain ⟨last,lr,ls,lh,lt⟩:=Tail.run terminal _ _ (total+1) (finishBudget z.B) base br
  have lr' : runFrom (Tail.last terminal) (finishBudget z.B)
      (restart a.final (Tail.last terminal).start)=some last := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some last
    rw [af]
    exact lr
  obtain ⟨r,rr,rs,rh,rt⟩:=Tail.join (Driver.machine worker) terminal
    (startHeads (z.heads b stack)) (scanData (z.bank b 0 stack) (total+1))
    (total*(bodyBudget z.B+2)+(total+1)+3) (finishBudget z.B) a last ar lr'
  have hs : saved=stack++stackWord (f.refs++[row.compiled.output.val]) := by
    simp only [saved,RecoveryBoundedClauseCollect.pushed,stackWord,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  let finished : Forward z b (randomnesses R 0 (total+1)):={
    next:=row.compiled.final,extension:=f.extension.trans row.compiled.extension,refs:=f.refs++[row.compiled.output.val]
    spine:=by
      rw [hall]
      apply f.spine.append
      exact Spine.cons (pcp:=compactProjectionPCP (p.normalized R Q hr hq)) (x:=x) (count:=count) (hc:=hc)
        f.next (bitInputOfCode R total) [] row.compiled.final []
        (Spine.nil (pcp:=compactProjectionPCP (p.normalized R Q hr hq)) (x:=x) (count:=count) (hc:=hc) row.compiled.final)
    refs_length:=by rw [hall,List.length_append,List.length_append,f.refs_length];rfl
    refs_bound:=by
      intro ref href
      rcases List.mem_append.mp href with he|he
      · exact f.refs_bound ref he
      · have he:=List.mem_singleton.mp he
        exact he ▸ row.compiled.output.isLt.le.trans (hrow.trans z.graph_bound)
    next_bound:=hrow }
  refine ⟨finished,r,rr,?_,?_,?_⟩
  · rw [rs,ls]
    unfold scanBudget
    omega
  · have he:=rh.trans (lh.trans (congrArg scanHeads bh))
    change r.final.heads=scanHeads (z.heads row.compiled.final saved) at he
    rw [hs] at he
    exact he
  · have he:=rt.trans (lt.trans (congrArg (fun A=>scanData A (total+1)) bt))
    change r.final.tapes=scanData (z.bank row.compiled.final total saved) (total+1) at he
    rw [hs] at he
    exact he

end Scan

noncomputable def scanMachine:=Scan.machine bodyMachine finishMachine

theorem scan_run (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (total : ℕ) (stack : List Bool) (hk : total<2^R)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R 0 (total+1))).final.nodes.length≤z.G) :
    ∃ f : Forward z b (randomnesses R 0 (total+1)), ∃ r,
      runFrom scanMachine (scanBudget z.B total)
        ⟨scanMachine.start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (total+1)⟩=some r ∧
      r.steps≤ scanBudget z.B total ∧
      r.final.heads=scanHeads (z.heads f.next (stack++stackWord f.refs)) ∧
      r.final.tapes=scanData (z.bank f.next total (stack++stackWord f.refs)) (total+1) := by
  exact Scan.scan_run bodyMachine finishMachine z z.body_original z.finish_original b total stack hk hFinal

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows

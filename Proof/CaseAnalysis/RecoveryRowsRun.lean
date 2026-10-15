import Proof.CaseAnalysis.RecoveryRowsFoldMeaning

/-! The complete original verifier-row graph: all physical row calls,
their paid driver, terminal true node, and exact reverse ANDs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Whole
variable {a b : ℕ}
def machine (first : Machine 116 a) (last : Machine 116 b):=Composition.machine first last
theorem join (first : Machine 116 a) (last : Machine 116 b) (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (u v : ℕ) (p : ExecutionReceipt 116 a) (q : ExecutionReceipt 116 b)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom last v (restart p.final last.start)=some q) :
    ∃ r,runFrom (machine first last) (u+1+v) ⟨(machine first last).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join first last _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Whole

noncomputable def machine:=Whole.machine scanMachine RecoveryBoundedRowsFold.machine
def budget (B W total : ℕ):=scanBudget B total+1+RecoveryBoundedGrammarFold.budget true (total+1) (capacity W)

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : ℕ} {hc : count≤bound}

noncomputable def foldResult (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (k : ℕ) (stack : List Bool):=
  RecoveryBoundedRowsFold.result b.nodes.length (capacity z.W) z.D (OuterPCPRecovery.boundedCircuitFieldLimit R bound)
    z.L z.B R count Q (Codec.clauses p).length (z.word b) (DedupBytes.fields p++z.sourceTail) stack z.packet refs
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) z.B)

theorem fold_ready (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (k : ℕ) (stack : List Bool)
    (href : ∀ ref∈refs,ref≤z.W) (ha : b.nodes.length+refs.length≤z.W) :
    ∃ r,runFrom RecoveryBoundedRowsFold.machine (RecoveryBoundedGrammarFold.budget true refs.length (capacity z.W))
      ⟨RecoveryBoundedRowsFold.machine.start,scanHeads (z.heads b (stack++stackWord refs)),
        scanData (z.bank b k (stack++stackWord refs)) refs.length⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarFold.budget true refs.length (capacity z.W) ∧
      r.final.heads=(foldResult z b refs k stack).heads ∧ r.final.tapes=(foldResult z b refs k stack).tapes := by
  exact RecoveryBoundedRowsFold.fold_run b.nodes.length z.W (capacity z.W) z.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L z.B R count Q (Codec.clauses p).length
    (z.word b) (DedupBytes.fields p++z.sourceTail) stack z.packet refs
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) z.B) href ha le_rfl
    (by have h:=z.backing_capacity;omega) z.backing_dock z.backing_log

namespace Assembly
variable {s t : ℕ}
theorem run (scanner : Machine 116 s) (folder : Machine 116 t) (z : Resources p R Q hr hq x count hc)
    (scanSupplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (total : ℕ) (stack : List Bool), total<2^R →
      (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (randomnesses R 0 (total+1))).final.nodes.length≤z.G →
      ∃ f : Forward z b (randomnesses R 0 (total+1)), ∃ r,
        runFrom scanner (scanBudget z.B total) ⟨scanner.start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (total+1)⟩=some r ∧
        r.steps≤ scanBudget z.B total ∧ r.final.heads=scanHeads (z.heads f.next (stack++stackWord f.refs)) ∧
        r.final.tapes=scanData (z.bank f.next total (stack++stackWord f.refs)) (total+1))
    (foldSupplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (k : ℕ) (stack : List Bool),
      (∀ ref∈refs,ref≤z.W) → b.nodes.length+refs.length≤z.W →
      ∃ r,runFrom folder (RecoveryBoundedGrammarFold.budget true refs.length (capacity z.W))
        ⟨folder.start,scanHeads (z.heads b (stack++stackWord refs)),scanData (z.bank b k (stack++stackWord refs)) refs.length⟩=some r ∧
        r.steps≤RecoveryBoundedGrammarFold.budget true refs.length (capacity z.W) ∧
        r.final.heads=(foldResult z b refs k stack).heads ∧ r.final.tapes=(foldResult z b refs k stack).tapes)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (total : ℕ) (stack : List Bool) (hk : total<2^R)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R 0 (total+1))).final.nodes.length≤z.G) :
    let original:=compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (randomnesses R 0 (total+1))
    ∃ f : Forward z b (randomnesses R 0 (total+1)), ∃ r,
      runFrom (Whole.machine scanner folder) (budget z.B z.W total)
        ⟨(Whole.machine scanner folder).start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (total+1)⟩=some r ∧
      r.steps≤budget z.B z.W total ∧
      r.final.heads=(foldResult z f.next f.refs total stack).heads ∧
      r.final.tapes=(foldResult z f.next f.refs total stack).tapes ∧
      r.final.tapes 20=z.word original.final ∧
      r.final.tapes 25=List.replicate original.output.val true := by
  let original:=compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (randomnesses R 0 (total+1))
  obtain ⟨f,a,ar,as,ah,aT⟩:=scanSupplier b total stack hk hFinal
  have hf:=f.spine.original
  change original.final.nodes=f.next.nodes++RecoveryBoundedNative.allSuffix (n:=descriptionWidth R bound) f.next.nodes.length f.refs ∧
    original.output.val=f.next.nodes.length+f.refs.length at hf
  have hcount : f.refs.length=total+1:=by simpa only [randomnesses,List.length_map,List.length_range'] using f.refs_length
  have hbound : f.next.nodes.length+f.refs.length≤z.W := by
    have h : original.output.val≤z.W:=original.output.isLt.le.trans (hFinal.trans z.graph_bound)
    rw [hf.2] at h
    exact h
  obtain ⟨last,lr,ls,lh,lt⟩:=foldSupplier f.next f.refs total stack f.refs_bound hbound
  rw [hcount] at lr ls
  have lr' : runFrom folder (RecoveryBoundedGrammarFold.budget true (total+1) (capacity z.W))
      (restart a.final folder.start)=some last := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some last
    rw [ah,aT]
    exact lr
  obtain ⟨r,rr,rs,rh,rt⟩:=Whole.join scanner folder
    (startHeads (z.heads b stack)) (scanData (z.bank b 0 stack) (total+1))
    (scanBudget z.B total) (RecoveryBoundedGrammarFold.budget true (total+1) (capacity z.W)) a last ar lr'
  have rH : r.final.heads=(foldResult z f.next f.refs total stack).heads:=rh.trans lh
  have rT : r.final.tapes=(foldResult z f.next f.refs total stack).tapes:=rt.trans lt
  refine ⟨f,r,rr,?_,rH,rT,?_,?_⟩
  · rw [rs]
    unfold budget
    omega
  · rw [rT]
    rw [foldResult,RecoveryBoundedRowsFold.result_graph _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (descriptionWidth R bound)]
    unfold Resources.word
    rw [hf.1,List.flatMap_append,List.append_assoc]
  · rw [rT,foldResult,RecoveryBoundedRowsFold.result_output,hf.2]

end Assembly

theorem run (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (total : ℕ) (stack : List Bool) (hk : total<2^R)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R 0 (total+1))).final.nodes.length≤z.G) :
    let original:=compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (randomnesses R 0 (total+1))
    ∃ f : Forward z b (randomnesses R 0 (total+1)), ∃ r,
      runFrom machine (budget z.B z.W total)
        ⟨machine.start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (total+1)⟩=some r ∧
      r.steps≤budget z.B z.W total ∧
      r.final.heads=(foldResult z f.next f.refs total stack).heads ∧
      r.final.tapes=(foldResult z f.next f.refs total stack).tapes ∧
      r.final.tapes 20=z.word original.final ∧
      r.final.tapes 25=List.replicate original.output.val true := by
  exact Assembly.run scanMachine RecoveryBoundedRowsFold.machine z (scan_run z) (fold_ready z) b total stack hk hFinal

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows

import Proof.CaseAnalysis.RecoveryCountConjunctionMeaning

/-! All original verifier rows followed by the one original fixed-count
AND. The entry is the actual grammar graph, saved output and incremented
node count; the enclosing grammar producer supplies that paid boundary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem append_word {arity : ℕ} (pre : List Bool) (b c : BooleanDAGBuilder arity) (node : BooleanNode arity)
    (h : c.nodes=b.nodes++[node]) :
    pre++b.nodes.flatMap PCPPRequestNodeSchema.native++PCPPRequestNodeSchema.native node=
      pre++c.nodes.flatMap PCPPRequestNodeSchema.native := by
  rw [h,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

noncomputable def machine:=Whole.machine RecoveryBoundedRows.machine RecoveryBoundedCountConjunction.machine
def budget (B W R : ℕ):=RecoveryBoundedRows.budget B W (2^R-1)+1+(24*capacity W+64)

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

noncomputable def result (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (ref : ℕ) (stack : List Bool):=
  RecoveryBoundedCountConjunction.result b.nodes.length (capacity z.W) z.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L z.B R (count.val+1) Q (Codec.clauses p).length
    ref (z.word b) (DedupBytes.fields p++z.sourceTail) stack z.packet refs
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R (2^R-1)) z.B)

theorem conjunction_ready (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (ref : ℕ) (stack : List Bool)
    (hRef : ref≤z.W) (ha : b.nodes.length+refs.length≤z.W) :
    ∃ r,runFrom RecoveryBoundedCountConjunction.machine (24*capacity z.W+64)
      ⟨RecoveryBoundedCountConjunction.machine.start,
        (foldResult z b refs (2^R-1) (RecoveryBoundedClauseCollect.pushed ref stack)).heads,
        (foldResult z b refs (2^R-1) (RecoveryBoundedClauseCollect.pushed ref stack)).tapes⟩=some r ∧
      r.steps≤24*capacity z.W+64 ∧
      r.final.heads=(result z b refs ref stack).heads ∧ r.final.tapes=(result z b refs ref stack).tapes :=
  RecoveryBoundedCountConjunction.run b.nodes.length (capacity z.W) z.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L z.B R (count.val+1) Q (Codec.clauses p).length
    ref (z.word b) (DedupBytes.fields p++z.sourceTail) stack z.packet refs
    (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R (2^R-1)) z.B) z.W hRef ha le_rfl

namespace Assembly
variable {s t : ℕ}
theorem run (rowsMachine : Machine 116 s) (andMachine : Machine 116 t)
    (z : Resources p R Q hr hq x (count.val+1) hc)
    (rowSupplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool),
      (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x (count.val+1) hc b (allRandomness R)).final.nodes.length≤z.G →
      ∃ f : Forward z b (allRandomness R), ∃ r,
        runFrom rowsMachine (RecoveryBoundedRows.budget z.B z.W (2^R-1))
          ⟨rowsMachine.start,startHeads (z.heads b stack),scanData (z.bank b 0 stack) (2^R)⟩=some r ∧
        r.steps≤RecoveryBoundedRows.budget z.B z.W (2^R-1) ∧
        r.final.heads=(foldResult z f.next f.refs (2^R-1) stack).heads ∧
        r.final.tapes=(foldResult z f.next f.refs (2^R-1) stack).tapes ∧
        r.final.tapes 20=z.word (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x (count.val+1) hc b (allRandomness R)).final ∧
        r.final.tapes 25=List.replicate (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x (count.val+1) hc b (allRandomness R)).output.val true)
    (andSupplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (ref : ℕ) (stack : List Bool),
      ref≤z.W → b.nodes.length+refs.length≤z.W →
      ∃ r,runFrom andMachine (24*capacity z.W+64)
        ⟨andMachine.start,(foldResult z b refs (2^R-1) (RecoveryBoundedClauseCollect.pushed ref stack)).heads,
          (foldResult z b refs (2^R-1) (RecoveryBoundedClauseCollect.pushed ref stack)).tapes⟩=some r ∧
        r.steps≤24*capacity z.W+64 ∧ r.final.heads=(result z b refs ref stack).heads ∧ r.final.tapes=(result z b refs ref stack).tapes)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    ∃ f : Forward z grammar.final (allRandomness R), ∃ r,
      runFrom (Whole.machine rowsMachine andMachine) (budget z.B z.W R)
        ⟨(Whole.machine rowsMachine andMachine).start,
          startHeads (z.heads grammar.final (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)),
          scanData (z.bank grammar.final 0 (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)) (2^R)⟩=some r ∧
      r.steps≤budget z.B z.W R ∧ r.final.heads=(result z f.next f.refs grammar.output.val stack).heads ∧
      r.final.tapes=(result z f.next f.refs grammar.output.val stack).tapes ∧
      r.final.tapes 20=z.word original.final ∧ r.final.tapes 25=List.replicate original.output.val true := by
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
  let rows:=compileVerifierRows pcp x (count.val+1) hc grammar.final (allRandomness R)
  let original:=compileFixedCount pcp x b count
  have hRows : rows.final.nodes.length≤z.G:=RecoveryBoundedCounts.fixed_rows_bound pcp x b count z.G hFinal
  have hRef : grammar.output.val≤z.W:=grammar.output.isLt.le.trans (rows.extension.length_le.trans (hRows.trans z.graph_bound))
  obtain ⟨f,a,ar,as,ah,aT,ag,_⟩:=rowSupplier grammar.final (RecoveryBoundedClauseCollect.pushed grammar.output.val stack) hRows
  have hf:=f.spine.original
  change rows.final.nodes=f.next.nodes++RecoveryBoundedNative.allSuffix (n:=descriptionWidth R bound) f.next.nodes.length f.refs ∧
    rows.output.val=f.next.nodes.length+f.refs.length at hf
  have ha : f.next.nodes.length+f.refs.length≤z.W := by
    rw [←hf.2]
    exact rows.output.isLt.le.trans (hRows.trans z.graph_bound)
  obtain ⟨last,lr,ls,lh,lt⟩:=andSupplier f.next f.refs grammar.output.val stack hRef ha
  have lr' : runFrom andMachine (24*capacity z.W+64) (restart a.final andMachine.start)=some last := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some last
    rw [ah,aT]
    exact lr
  obtain ⟨r,rr,rs,rh,rt⟩:=Whole.join rowsMachine andMachine
    (startHeads (z.heads grammar.final (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)))
    (scanData (z.bank grammar.final 0 (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)) (2^R))
    (RecoveryBoundedRows.budget z.B z.W (2^R-1)) (24*capacity z.W+64) a last ar lr'
  have rH:=rh.trans lh
  have rT:=rt.trans lt
  refine ⟨f,r,rr,?_,rH,rT,?_,?_⟩
  · rw [rs]
    unfold budget
    omega
  · rw [rT,result,RecoveryBoundedCountConjunction.result_graph _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (descriptionWidth R bound)]
    change (foldResult z f.next f.refs (2^R-1) (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)).tapes 20++
      PCPPRequestNodeSchema.native (.and grammar.output.val (f.next.nodes.length+f.refs.length))=z.word original.final
    rw [←aT,ag,←hf.2]
    exact append_word z.pre rows.final original.final (.and grammar.output.val rows.output.val)
      (RecoveryBoundedCounts.fixed_nodes pcp x b count)
  · rw [rT,result,RecoveryBoundedCountConjunction.result_output,←hf.2]
    have hs:=RecoveryBoundedCounts.rows_output_succ pcp x grammar.final (count.val+1) hc (allRandomness R)
    change List.replicate (rows.output.val+1) true=List.replicate original.output.val true
    have ho : original.output.val=rows.final.nodes.length:=RecoveryBoundedCounts.fixed_output pcp x b count
    exact congrArg (fun value=>List.replicate value true) (hs.trans ho.symm)

end Assembly

theorem run (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    ∃ f : Forward z grammar.final (allRandomness R), ∃ r,
      runFrom machine (budget z.B z.W R)
        ⟨machine.start,startHeads (z.heads grammar.final (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)),
          scanData (z.bank grammar.final 0 (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)) (2^R)⟩=some r ∧
      r.steps≤budget z.B z.W R ∧ r.final.heads=(result z f.next f.refs grammar.output.val stack).heads ∧
      r.final.tapes=(result z f.next f.refs grammar.output.val stack).tapes ∧
      r.final.tapes 20=z.word original.final ∧ r.final.tapes 25=List.replicate original.output.val true :=
  Assembly.run RecoveryBoundedRows.machine RecoveryBoundedCountConjunction.machine z (all_run z) (conjunction_ready z) b stack hFinal

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows

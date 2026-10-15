import Proof.CaseAnalysis.RecoveryFixedRestart

/-! The actual original fixed-count output is saved and its same row bank
is reloaded, using only the existing row resources and paid stack capacity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem save_run (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (P : ℕ)
    (f : Forward z (compileExpr b (fixedCountGrammarExpr (n:=R) count)).final (allRandomness R))
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G)
    (hGraph : (result z f.next f.refs (compileExpr b (fixedCountGrammarExpr (n:=R) count)).output.val stack).tapes 20=
      z.word (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final)
    (hOutput : f.next.nodes.length+f.refs.length+1=
      (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).output.val)
    (hP : stack.length+(2^R+1)*(2*z.W+1)≤P) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    ∃ r,runFrom RecoveryBoundedFixedContinue.machine (64*(z.B+2))
      ⟨RecoveryBoundedFixedContinue.machine.start,(result z f.next f.refs grammar.output.val stack).heads,
        stackPadded P (result z f.next f.refs grammar.output.val stack).tapes⟩=some r ∧
      r.steps≤64*(z.B+2) ∧ r.final.heads=RecoveryBoundedFixedRestart.heads (z.word original.final) saved ∧
      r.final.tapes=RecoveryBoundedFixedRestart.data P (z.rowBank original.final saved)
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R (2^R-1)) z.B) (2^R) := by
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
  let original:=compileFixedCount pcp x b count
  let fields:=RecoveryBoundedRowPrototype.fields (capacity z.W) z.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L R (count.val+1) Q (Codec.clauses p).length
  let proj:=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R (2^R-1)) z.B
  have hC : capacity z.W+1≤z.B:=by have h:=z.backing_capacity;omega
  have hlen : f.refs.length=2^R:=by simpa only [allRandomness,List.length_map,List.length_range] using f.refs_length
  have hg : grammar.output.val≤z.W:=
    grammar.output.isLt.le.trans ((compileVerifierRows pcp x (count.val+1) hc grammar.final (allRandomness R)).extension.length_le.trans
      ((RecoveryBoundedCounts.fixed_rows_bound pcp x b count z.G hFinal).trans z.graph_bound))
  have ho : original.output.val≤z.W:=original.output.isLt.le.trans (hFinal.trans z.graph_bound)
  have hRef : 2*(f.next.nodes.length+f.refs.length+1)+2≤z.B:=by
    rw [hOutput]
    have h:=z.backing_capacity
    unfold capacity at h
    nlinarith [Nat.zero_le (z.W^2)]
  have hs : stack.length+(2*grammar.output.val+1+
      (RecoveryBoundedCountConjunction.state f.next.nodes.length (z.word f.next) f.refs).erased)≤P:=
    RecoveryBoundedFixedFinish.erased_bound f.next.nodes.length z.W grammar.output.val (z.word f.next) stack f.refs P
      hg f.refs_bound (by rw [hlen];exact hP)
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedFixedFinish.result_run f.next.nodes.length (capacity z.W) z.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L z.B R (count.val+1) Q (Codec.clauses p).length
    grammar.output.val (z.word f.next) (DedupBytes.fields p++z.sourceTail) stack f.refs proj fields z.packetTail P hC
    (RecoveryBoundedFixedFinish.ambient_work_bound f.next.nodes.length (capacity z.W) z.D
      (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L z.B R (count.val+1) Q (Codec.clauses p).length
      (z.word f.next) (DedupBytes.fields p++z.sourceTail) (RecoveryBoundedClauseCollect.pushed grammar.output.val stack)
      z.packet f.refs proj hC z.backing_dock z.backing_log z.metadata_bound)
    hs hRef z.metadata_bound z.packet_bound
  have hb:=RecoveryBoundedFixedFinish.budget_bound (f.next.nodes.length+f.refs.length+1) z.B fields hRef z.metadata_bound
  have whole:=runFrom_moreFuel RecoveryBoundedFixedContinue.machine _
    (64*(z.B+2)-RecoveryBoundedGrammarAfter.budget (f.next.nodes.length+f.refs.length+1) z.B fields) _ r rr
  rw [Nat.add_sub_of_le hb] at whole
  refine ⟨r,whole,rs.trans hb,?_,?_⟩
  · change r.final.heads=RecoveryBoundedFixedRestart.heads (z.word original.final)
      (RecoveryBoundedAddress.pushed original.output.val stack)
    change r.final.heads=RecoveryBoundedFixedContinue.heads
      ((result z f.next f.refs grammar.output.val stack).tapes 20)
      (RecoveryBoundedAddress.pushed (f.next.nodes.length+f.refs.length+1) stack)
      RecoveryBoundedFixedFinish.extraHeads at rh
    rw [hGraph,hOutput] at rh
    exact rh
  · change r.final.tapes=RecoveryBoundedFixedContinue.data P
      (RecoveryBoundedGrammarBank.ready fields (f.next.nodes.length+f.refs.length+1+1) z.B
        ((result z f.next f.refs grammar.output.val stack).tapes 20)
        (RecoveryBoundedAddress.pushed (f.next.nodes.length+f.refs.length+1) stack) z.packet
        (DedupBytes.fields p++z.sourceTail))
      (Fin.addCases (m:=37) (n:=1) proj (fun _=>VerifierDecoding.CompareMachine.word f.refs.length)) at rt
    rw [hGraph,hOutput,RecoveryBoundedFixedFinish.ready_original _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hC z.backing_dock z.backing_log,hlen,RecoveryBoundedCounts.fixed_output_succ pcp x b count] at rt
    exact rt

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedRows

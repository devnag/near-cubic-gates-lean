import Proof.CaseAnalysis.RecoveryCountNativeFoldRun

/-! The original ascending count scan hands its exact saved references to
the original terminal false and reverse OR. No count or graph prepass occurs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

noncomputable def Resources.foldResult (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool)
    (refs : List ℕ) (extra : Fin 12→List Bool):=
  RecoveryBoundedCountNativeFold.result b.nodes.length (capacity z.base.W) z.base.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L z.base.B z.P R bound Q
    (Codec.clauses p).length (2^R) (z.base.word b) (DedupBytes.fields p++z.base.sourceTail)
    stack (z.packet bound) refs (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B)
    (RecoveryBoundedGrammarCold.metadata R bound 0 (capacity z.base.W) z.base.B (extraAt z.base.B bound extra))
    (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1)))
    (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1)))

theorem Resources.fold_data (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool)
    (refs : List ℕ) (extra : Fin 12→List Bool) (hb : 0<bound) (hlen : refs.length=bound) :
    scanData (z.bank b bound (stack++stackWord refs) extra) bound=
    RecoveryBoundedCountNativeFold.bank b.nodes.length (capacity z.base.W) z.base.D
      (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L z.base.B z.P R bound Q
      (Codec.clauses p).length (2^R) (z.base.word b) (DedupBytes.fields p++z.base.sourceTail)
      stack (z.packet bound) refs (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B)
      (RecoveryBoundedGrammarCold.metadata R bound 0 (capacity z.base.W) z.base.B (extraAt z.base.B bound extra))
      (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1)))
      (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1))) := by
  simp only [bank,currentFields,currentPacket,Nat.ne_of_gt hb,if_false,fields,
    RecoveryBoundedCountNativeFold.bank,hlen]

theorem Resources.finish_run (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool)
    (f : Forward z b (List.finRange bound)) (hb : 0<bound)
    (hFinal : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b
      (List.finRange bound)).final.nodes.length≤z.base.G) :
    ∃ r,runFrom RecoveryBoundedCountNativeFold.machine
      (RecoveryBoundedGrammarFold.budget false bound (capacity z.base.W))
      ⟨RecoveryBoundedCountNativeFold.machine.start,scanHeads (z.heads f.next (stack++stackWord f.refs)) 1,
        scanData (z.bank f.next bound (stack++stackWord f.refs) extra) bound⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarFold.budget false bound (capacity z.base.W) ∧
      r.final.heads=(z.foldResult f.next stack f.refs extra).heads ∧
      r.final.tapes=(z.foldResult f.next stack f.refs extra).tapes := by
  have hlen : f.refs.length=bound:=f.refs_length.trans List.length_finRange
  have original:=f.spine.original
  have ha : f.next.nodes.length+f.refs.length≤z.base.W := by
    have h:=(compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b
      (List.finRange bound)).output.isLt.le.trans (hFinal.trans z.base.graph_bound)
    rw [original.2] at h
    exact h
  have h:=RecoveryBoundedCountNativeFold.fold_run f.next.nodes.length z.base.W (capacity z.base.W)
    z.base.D (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L z.base.B z.P R bound Q
    (Codec.clauses p).length (2^R) (z.base.word f.next) (DedupBytes.fields p++z.base.sourceTail)
    stack (z.packet bound) f.refs (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B)
    (RecoveryBoundedGrammarCold.metadata R bound 0 (capacity z.base.W) z.base.B (extraAt z.base.B bound extra))
    (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1)))
    (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1))) f.refs_bound ha (Nat.le_refl _)
    (by have h:=z.base.backing_capacity;omega) z.base.backing_dock z.base.backing_log
  rw [←z.fold_data f.next stack f.refs extra hb hlen,hlen] at h
  exact h

private theorem native_append {q : ℕ} (pre : List Bool) (left suffix result : List (BooleanNode q))
    (h : result=left++suffix) :
    pre++left.flatMap PCPPRequestNodeSchema.native++suffix.flatMap PCPPRequestNodeSchema.native=
      pre++result.flatMap PCPPRequestNodeSchema.native := by
  rw [h,List.flatMap_append,List.append_assoc]

theorem Resources.finish_graph (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool)
    (f : Forward z b (List.finRange bound)) :
    (z.foldResult f.next stack f.refs extra).tapes 20=
      z.base.word (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b (List.finRange bound)).final := by
  have h:=RecoveryBoundedCountNativeFold.result_graph f.next.nodes.length (capacity z.base.W) z.base.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L z.base.B z.P R bound Q
    (Codec.clauses p).length (2^R) (z.base.word f.next) (DedupBytes.fields p++z.base.sourceTail)
    stack (z.packet bound) f.refs (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B)
    (RecoveryBoundedGrammarCold.metadata R bound 0 (capacity z.base.W) z.base.B (extraAt z.base.B bound extra))
    (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1)))
    (ZeroPadding.pad z.base.B (CompareMachine.word (bound+1))) (descriptionWidth R bound)
  change (z.foldResult f.next stack f.refs extra).tapes 20=_ at h
  exact h.trans (native_append z.base.pre f.next.nodes
    (RecoveryBoundedCounts.anySuffix f.next.nodes.length f.refs) _ f.spine.original.1)

theorem Resources.finish_output (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool)
    (f : Forward z b (List.finRange bound)) :
    (z.foldResult f.next stack f.refs extra).tapes 25=
      List.replicate (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b
        (List.finRange bound)).output.val true := by
  rw [f.spine.original.2]
  exact RecoveryBoundedCountNativeFold.result_output _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform

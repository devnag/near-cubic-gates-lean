import Proof.CaseAnalysis.RecoveryCountAfterRows

/-! Whole original fixed-count continuation after grammar: restore the
four scalars, advance the shared candidate, print/reload original row fields,
compile all verifier rows and final AND, then refresh the next finite driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows
open RecoveryBoundedGrammarCold (Room Allocation selectedFields selectedWord foldRows metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def afterGrammar:=Join.machine afterRows RecoveryBoundedCountDriverDock.machine
def afterGrammarBudget (C D F L R count Q clauses B W : ℕ):=
  afterRowsBudget C D F L R count Q clauses B W+1+RecoveryBoundedGrammarDriverBank.refreshBudget B (count+1)

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem afterGrammar_run (z : Resources p R Q hr hq x (count.val+1) hc) (P : ℕ)
    (room : Room z.W (RecoveryBoundedSelectorLoop.capacity z.W) z.D z.L z.S z.B P)
    (alloc : Allocation R bound z.G z.W)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (extra : Fin 12→List Bool)
    (hclauses : (Codec.clauses p).length≤z.W)
    (rawCount : extra 1=RecoveryBoundedGrammarScalarAdd.unary z.B count.val)
    (rawQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary z.B Q)
    (rawClauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary z.B (Codec.clauses p).length)
    (rawR : extra 5=RecoveryBoundedGrammarScalarAdd.unary z.B (R+1))
    (hTail : z.packetTail=List.replicate (z.B-(RecoveryBoundedRowReload.word
      (RecoveryBoundedRowPrototype.fields (RecoveryBoundedSelectorLoop.capacity z.W) z.D
        (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L R (count.val+1) Q (Codec.clauses p).length)).length) false)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G)
    (hP : stack.length+(2^R+1)*(2*z.W+1)≤P) :
    let C:=RecoveryBoundedSelectorLoop.capacity z.W
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let before:=RecoveryBoundedAddress.pushed grammar.output.val stack
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    let proj:=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B
    ∃ r,runFrom afterGrammar (afterGrammarBudget C z.D F z.L R count.val Q (Codec.clauses p).length z.B z.W)
      ⟨afterGrammar.start,RecoveryBoundedCountBank.heads (z.word grammar.final) before 1 1,
        RecoveryBoundedCountBank.data z.B P
          (RecoveryBoundedGrammarBank.ready (selectedFields foldRows R bound (bound+1) C)
            grammar.final.nodes.length z.B (z.word grammar.final) before
            (ZeroPadding.pad z.B (selectedWord foldRows R bound (bound+1) C)) (DedupBytes.fields p++z.sourceTail))
          proj (2^R) (metadata R bound (bound+1) C z.B extra)
          (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1)))
          (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+1)))⟩=some r ∧
      r.steps≤afterGrammarBudget C z.D F z.L R count.val Q (Codec.clauses p).length z.B z.W ∧
      r.final.heads=RecoveryBoundedCountBank.heads (z.word original.final) saved 1 1 ∧
      r.final.tapes=RecoveryBoundedCountBank.data z.B P (z.rowBank original.final saved) proj (2^R)
        (metadata R bound 0 C z.B (RecoveryBoundedCountPacketBank.nextExtra z.B count.val extra))
        (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1)))
        (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+2))) := by
  dsimp only
  let C:=RecoveryBoundedSelectorLoop.capacity z.W
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
  let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
  let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
  let before:=RecoveryBoundedAddress.pushed grammar.output.val stack
  let saved:=RecoveryBoundedAddress.pushed original.output.val stack
  let proj:=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B
  let source:=DedupBytes.fields p++z.sourceTail
  let nextFields:=RecoveryBoundedRowPrototype.fields C z.D F z.L R (count.val+1) Q (Codec.clauses p).length
  let nextExtra:=RecoveryBoundedCountPacketBank.nextExtra z.B count.val extra
  let bd:=ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1))
  let cd:=ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+1))
  obtain ⟨joined,jr,js,jh,jt⟩:=afterRows_run z P room alloc b stack extra hclauses rawCount rawQ rawClauses rawR
    hTail hFinal hP
  have hbound:=(alloc.scalars (⟨0,by omega⟩ : Fin (bound+1))).limit 5
  change bound+1≤z.W at hbound
  have hdriver:=(RecoveryBoundedGrammarCold.driver_fits room hbound count.isLt).2
  obtain ⟨last,lr,ls,lh,lt⟩:=RecoveryBoundedCountDriverDock.run R bound C count.val z.B P original.final.nodes.length
    (2^R) nextFields (z.word original.final) saved z.packet source proj nextExtra rfl hdriver
  have jt' : joined.final.tapes=RecoveryBoundedCountBank.data z.B P
      (RecoveryBoundedGrammarBank.ready nextFields original.final.nodes.length z.B
        (z.word original.final) saved z.packet source) proj (2^R)
      (metadata R bound 0 C z.B nextExtra) bd cd := by
    rw [jt,RecoveryBoundedCountRowsDock.row_ready z original.final saved]
    rfl
  have lt' : last.final.tapes=RecoveryBoundedCountBank.data z.B P (z.rowBank original.final saved) proj (2^R)
      (metadata R bound 0 C z.B nextExtra) bd (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+2))) := by
    rw [RecoveryBoundedCountRowsDock.row_ready z original.final saved]
    exact lt
  obtain ⟨whole,wr,ws,wh,wt⟩:=Join.resume_join afterRows RecoveryBoundedCountDriverDock.machine
    _ _ _ _ _ _ joined last jr jh jt' lr
  refine ⟨whole,wr,?_,wh.trans lh,wt.trans lt'⟩
  rw [ws]
  exact Nat.add_le_add (Nat.add_le_add_right js 1) ls

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline

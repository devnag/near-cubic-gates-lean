import Proof.CaseAnalysis.RecoveryCountGrammarBank

/-! Dock the entire original randomness-and-AND continuation into the
shared count bank; grammar metadata and both grammar drivers are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountRowsDock
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : ℕ} {hc : count≤bound}

theorem row_ready (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) :
    z.rowBank b stack=RecoveryBoundedGrammarBank.ready
      (RecoveryBoundedRowPrototype.fields (RecoveryBoundedSelectorLoop.capacity z.W) z.D
        (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L R count Q (Codec.clauses p).length)
      b.nodes.length z.B (z.word b) stack z.packet (DedupBytes.fields p++z.sourceTail) := by
  exact (RecoveryBoundedFixedFinish.ready_original _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by have h:=z.backing_capacity;omega) z.backing_dock z.backing_log).symm

theorem input (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (P : ℕ) :
    RecoveryBoundedFixedRows.stackPadded P (scanData (z.bank b 0 stack) (2^R))=
      RecoveryBoundedFixedRestart.data P (z.rowBank b stack)
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B) (2^R) := by
  funext i
  fin_cases i <;> simp [RecoveryBoundedFixedRows.stackPadded,RecoveryBoundedFixedRows.stackCapacity,
    scanData,Resources.bank,data,RecoveryBoundedFixedRestart.data,RecoveryBoundedFixedRestart.extra,
    RecoveryBoundedFixedContinue.data,RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,
    ZeroPadding.pad_zero,Fin.addCases]

noncomputable def machine:=TapeEmbedding.machine 36 RecoveryBoundedFixedRows.reusableMachine

theorem run {count : Fin bound} {hc : count.val+1≤bound}
    (z : Resources p R Q hr hq x (count.val+1) hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack : List Bool) (P : ℕ)
    (cold : Fin 33→List Bool) (bd cd : List Bool)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G)
    (hP : stack.length+(2^R+1)*(2*z.W+1)≤P) :
    let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
    let before:=RecoveryBoundedClauseCollect.pushed grammar.output.val stack
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    ∃ r,runFrom machine (RecoveryBoundedFixedRows.reusableBudget z.B z.W R)
      ⟨machine.start,RecoveryBoundedCountBank.heads (z.word grammar.final) before 1 1,
        RecoveryBoundedCountBank.data z.B P (z.rowBank grammar.final before)
          (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B) (2^R) cold bd cd⟩=some r ∧
      r.steps≤RecoveryBoundedFixedRows.reusableBudget z.B z.W R ∧
      r.final.heads=RecoveryBoundedCountBank.heads (z.word original.final) saved 1 1 ∧
      r.final.tapes=RecoveryBoundedCountBank.data z.B P (z.rowBank original.final saved)
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B) (2^R) cold bd cd := by
  dsimp only
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedFixedRows.reusable_run z b stack P hFinal hP
  rw [input] at ar
  let eH:=RecoveryBoundedCountBank.extraHeads 1 1
  let eT:=RecoveryBoundedCountBank.extras z.B cold bd cd
  have rr:=TapeEmbedding.run_embed RecoveryBoundedFixedRows.reusableMachine eH eT _ _ a ar
  refine ⟨TapeEmbedding.receipt eH eT a,rr,as,?_,?_⟩
  · change Fin.addCases (m:=116) (n:=36) (motive:=fun _ : Fin 152=>ℕ) a.final.heads eH=_
    rw [ah]
    rfl
  · change Fin.addCases (m:=116) (n:=36) (motive:=fun _ : Fin 152=>List Bool) a.final.tapes eT=_
    rw [atapes]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountRowsDock

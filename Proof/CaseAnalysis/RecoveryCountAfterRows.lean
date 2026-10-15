import Proof.CaseAnalysis.RecoveryCountAfterPacket

/-! Whole original grammar-to-row continuation: restore the four scalars,
advance the shared candidate, reload the literal row fields, and compile every
original verifier row and the fixed-count AND. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows
open RecoveryBoundedGrammarCold (Room Allocation selectedFields selectedWord foldRows metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Join
theorem resume_join {s t : ℕ} (first : Machine 152 s) (last : Machine 152 t)
    (u v : ℕ) (H H' : Fin 152→ℕ) (A A' : Fin 152→List Bool)
    (p : ExecutionReceipt 152 s) (q : ExecutionReceipt 152 t)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hh : p.final.heads=H') (ht : p.final.tapes=A')
    (hq : runFrom last v ⟨last.start,H',A'⟩=some q) :
    ∃ r,runFrom (machine first last) (u+1+v) ⟨(machine first last).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  apply run first last u v H A p q hp
  change runFrom last v ⟨last.start,p.final.heads,p.final.tapes⟩=some q
  rw [hh,ht]
  exact hq
end Join

noncomputable def afterRows:=Join.machine afterPacket RecoveryBoundedCountRowsDock.machine
def afterRowsBudget (C D F L R count Q clauses B W : ℕ):=
  afterPacketBudget C D F L R count Q clauses B+1+RecoveryBoundedFixedRows.reusableBudget B W R

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem afterRows_run (z : Resources p R Q hr hq x (count.val+1) hc) (P : ℕ)
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
    ∃ r,runFrom afterRows (afterRowsBudget C z.D F z.L R count.val Q (Codec.clauses p).length z.B z.W)
      ⟨afterRows.start,RecoveryBoundedCountBank.heads (z.word grammar.final) before 1 1,
        RecoveryBoundedCountBank.data z.B P
          (RecoveryBoundedGrammarBank.ready (selectedFields foldRows R bound (bound+1) C)
            grammar.final.nodes.length z.B (z.word grammar.final) before
            (ZeroPadding.pad z.B (selectedWord foldRows R bound (bound+1) C)) (DedupBytes.fields p++z.sourceTail))
          proj (2^R) (metadata R bound (bound+1) C z.B extra)
          (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1)))
          (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+1)))⟩=some r ∧
      r.steps≤afterRowsBudget C z.D F z.L R count.val Q (Codec.clauses p).length z.B z.W ∧
      r.final.heads=RecoveryBoundedCountBank.heads (z.word original.final) saved 1 1 ∧
      r.final.tapes=RecoveryBoundedCountBank.data z.B P (z.rowBank original.final saved) proj (2^R)
        (metadata R bound 0 C z.B (RecoveryBoundedCountPacketBank.nextExtra z.B count.val extra))
        (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1)))
        (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+1))) := by
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
  have packetEq : z.packet=RecoveryBoundedCountPacketCanonical.packet C z.D F z.L R (count.val+1) Q (Codec.clauses p).length z.B := by
    simp only [Resources.packet,hTail,RecoveryBoundedCountPacketCanonical.packet,ZeroPadding.pad]
    rfl
  have rowReady (g : BooleanDAGBuilder (descriptionWidth R bound)) (s : List Bool) :
      RecoveryBoundedGrammarBank.ready nextFields g.nodes.length z.B (z.word g) s
        (RecoveryBoundedCountPacketCanonical.packet C z.D F z.L R (count.val+1) Q (Codec.clauses p).length z.B) source=
      z.rowBank g s := by
    rw [←packetEq]
    exact (RecoveryBoundedCountRowsDock.row_ready z g s).symm
  obtain ⟨a,ar,as,ah,atapes⟩:=afterPacket_run room alloc count Q (Codec.clauses p).length grammar.final.nodes.length
    (2^R) (z.word grammar.final) before source proj extra bd cd z.query_bound hclauses rawCount rawQ rawClauses rawR
    z.metadata_bound z.packet_bound
  rw [rowReady grammar.final before] at atapes
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedCountRowsDock.run z b stack P (metadata R bound 0 C z.B nextExtra) bd cd hFinal hP
  obtain ⟨joined,jr,js,jh,jt⟩:=Join.resume_join afterPacket RecoveryBoundedCountRowsDock.machine
    _ _ _ _ _ _ a r ar ah atapes rr
  refine ⟨joined,jr,?_,jh.trans rh,jt.trans rt⟩
  rw [js]
  exact Nat.add_le_add (Nat.add_le_add_right as 1) rs

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline

import Proof.CaseAnalysis.RecoveryCountAfterGrammar

/-! One complete reusable original fixed-count compiler. The exact graph
and saved output are returned with the paid next-candidate metadata/driver;
the following count uses the same original row/projection bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline
open LocalBitMultitape Composition SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedRows
open RecoveryBoundedGrammarCold (Room Allocation metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Join
theorem endpoints {s t : ℕ} (first : Machine 152 s) (last : Machine 152 t)
    (u v : ℕ) (H H' H'' : Fin 152→ℕ) (A A' A'' : Fin 152→List Bool)
    (hp : ∃ p,runFrom first u ⟨first.start,H,A⟩=some p ∧ p.steps≤u ∧
      p.final.heads=H' ∧ p.final.tapes=A')
    (hq : ∃ q,runFrom last v ⟨last.start,H',A'⟩=some q ∧ q.steps≤v ∧
      q.final.heads=H'' ∧ q.final.tapes=A'') :
    ∃ r,runFrom (machine first last) (u+1+v) ⟨(machine first last).start,H,A⟩=some r ∧
      r.steps≤u+1+v ∧ r.final.heads=H'' ∧ r.final.tapes=A'' := by
  obtain ⟨p,pr,ps,ph,pt⟩:=hp
  obtain ⟨q,qr,qs,qh,qt⟩:=hq
  obtain ⟨r,rr,rs,rh,rt⟩:=resume_join first last u v H H' A A' p q pr ph pt qr
  refine ⟨r,rr,?_,rh.trans qh,rt.trans qt⟩
  rw [rs]
  exact Nat.add_le_add (Nat.add_le_add_right ps 1) qs
end Join

noncomputable def front:=Join.machine RecoveryBoundedCountGrammarBank.entry RecoveryBoundedCountGrammarBank.compiled
noncomputable def machine:=Join.machine front afterGrammar
def budget (C D F L R count Q clauses B W bound : ℕ):=
  (RecoveryBoundedGrammarCold.atomBudget B+1+RecoveryBoundedGrammarCold.compiledBudget B bound count)+1+
    afterGrammarBudget C D F L R count Q clauses B W

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : Fin bound} {hc : count.val+1≤bound}

theorem run (z : Resources p R Q hr hq x (count.val+1) hc) (P : ℕ)
    (room : Room z.W (RecoveryBoundedSelectorLoop.capacity z.W) z.D z.L z.S z.B P)
    (alloc : Allocation R bound z.G z.W)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (stack packet : List Bool)
    (current : Fin 78→List Bool) (extra : Fin 12→List Bool)
    (hclauses : (Codec.clauses p).length≤z.W)
    (rawWidth : extra 0=RecoveryBoundedGrammarScalarAdd.unary z.B (rowWidth R bound))
    (rawCount : extra 1=RecoveryBoundedGrammarScalarAdd.unary z.B count.val)
    (rawQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary z.B Q)
    (rawClauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary z.B (Codec.clauses p).length)
    (rawR : extra 5=RecoveryBoundedGrammarScalarAdd.unary z.B (R+1))
    (hTail : z.packetTail=List.replicate (z.B-(RecoveryBoundedRowReload.word
      (RecoveryBoundedRowPrototype.fields (RecoveryBoundedSelectorLoop.capacity z.W) z.D
        (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.L R (count.val+1) Q (Codec.clauses p).length)).length) false)
    (hCurrent : ∀ j∈RecoveryBoundedRowReload.ports,(current j).length≤z.B) (hPacket : packet.length≤z.B)
    (hSource : (DedupBytes.fields p++z.sourceTail).length≤z.B)
    (hStack : stack.length+z.W*(2*z.W+1)≤z.S)
    (hFinal : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.G)
    (hP : stack.length+(2^R+1)*(2*z.W+1)≤P) :
    let C:=RecoveryBoundedSelectorLoop.capacity z.W
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    let proj:=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B
    ∃ r,runFrom machine (budget C z.D F z.L R count.val Q (Codec.clauses p).length z.B z.W bound)
      ⟨machine.start,RecoveryBoundedCountBank.heads (z.word b) stack 1 1,
        RecoveryBoundedCountBank.data z.B P
          (RecoveryBoundedGrammarBank.ready current b.nodes.length z.B (z.word b) stack packet (DedupBytes.fields p++z.sourceTail))
          proj (2^R) (metadata R bound 0 C z.B extra)
          (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1)))
          (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+1)))⟩=some r ∧
      r.steps≤budget C z.D F z.L R count.val Q (Codec.clauses p).length z.B z.W bound ∧
      r.final.heads=RecoveryBoundedCountBank.heads (z.word original.final) saved 1 1 ∧
      r.final.tapes=RecoveryBoundedCountBank.data z.B P (z.rowBank original.final saved) proj (2^R)
        (metadata R bound 0 C z.B (RecoveryBoundedCountPacketBank.nextExtra z.B count.val extra))
        (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (bound+1)))
        (ZeroPadding.pad z.B (VerifierDecoding.CompareMachine.word (count.val+2))) := by
  dsimp only
  let C:=RecoveryBoundedSelectorLoop.capacity z.W
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  let grammar:=compileExpr b (fixedCountGrammarExpr (n:=R) count)
  let proj:=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.B
  let source:=DedupBytes.fields p++z.sourceTail
  have scalars:=alloc.scalars (⟨0,by omega⟩ : Fin (bound+1))
  have a:=RecoveryBoundedCountGrammarBank.entry_run room scalars current b.nodes.length count.val
    (2^R) (z.word b) stack packet source proj extra hPacket hCurrent
  have grammarBound : grammar.final.nodes.length≤z.G:=
    (compileVerifierRows pcp x (count.val+1) hc grammar.final (allRandomness R)).extension.length_le.trans
      (RecoveryBoundedCounts.fixed_rows_bound pcp x b count z.G hFinal)
  have g:=RecoveryBoundedCountGrammarBank.compiled_run room alloc b count z.pre stack source proj (2^R) extra
    grammarBound z.output_bound hStack hSource rawWidth
  have joined:=Join.endpoints RecoveryBoundedCountGrammarBank.entry RecoveryBoundedCountGrammarBank.compiled
    _ _ _ _ _ _ _ _ a g
  have last:=afterGrammar_run z P room alloc b stack extra hclauses rawCount rawQ rawClauses rawR
    hTail hFinal hP
  exact Join.endpoints front afterGrammar _ _ _ _ _ _ _ _ joined last

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline

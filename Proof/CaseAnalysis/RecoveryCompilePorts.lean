import Proof.CaseAnalysis.RecoveryPreparedBank
import Proof.CaseAnalysis.RecoveryGraphSerializeEntry

/-! The literal completed count circuit supplies exactly the unchanged
cold serializer's seven ports, with all fresh serializer tapes empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdCompile
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedCountUniform
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem fold_retained_heads (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) (i : Fin 6) :
    (z.foldResult b [] refs (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).heads
      (RecoveryBoundedCountNativeFold.retainedPorts i)=0 := by
  apply RecoveryBoundedCountNativeFold.retained_heads

theorem fold_retained_words (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (refs : List ℕ) :
    (fun i=>(z.foldResult b [] refs
      (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).tapes
        (RecoveryBoundedCountNativeFold.retainedPorts i))=
    (![ZeroPadding.pad z.base.B (List.replicate R true),
      ZeroPadding.pad z.base.B (List.replicate bound true),
      ZeroPadding.pad z.base.B (List.replicate (descriptionWidth R bound) true),
      List.replicate z.base.B false,List.replicate z.base.B true,List.replicate z.base.B false] : Fin 6→List Bool) := by
  have h:=RecoveryBoundedCountNativeFold.retained_words b.nodes.length
    (RecoveryBoundedSelectorLoop.capacity z.base.W) z.base.D
    (OuterPCPRecovery.boundedCircuitFieldLimit R bound) z.base.L z.base.B z.P R bound Q
    (Codec.clauses p).length (2^R) (z.base.word b) (DedupBytes.fields p++z.base.sourceTail)
    [] (z.packet bound) refs (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B)
    (RecoveryBoundedGrammarCold.metadata R bound 0 (RecoveryBoundedSelectorLoop.capacity z.base.W) z.base.B
      (extraAt z.base.B bound (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)))
    (ZeroPadding.pad z.base.B (VerifierDecoding.CompareMachine.word (bound+1)))
    (ZeroPadding.pad z.base.B (VerifierDecoding.CompareMachine.word (bound+1)))
  change (fun i=>(z.foldResult b [] refs
    (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).tapes
      (RecoveryBoundedCountNativeFold.retainedPorts i))=_ at h
  rw [h]
  funext i
  fin_cases i <;>
    simp [RecoveryBoundedGrammarCold.metadata,RecoveryBoundedGrammarCold.numbers,extraAt,
      RecoveryBoundedColdPrepared.extra,RecoveryBoundedColdMetadata.extra,
      RecoveryBoundedColdMetadata.extraValues,RecoveryBoundedGrammarScalarAdd.unary,
      descriptionWidth,Nat.mul_comm,Fin.addCases,ZeroPadding.pad]
  all_goals rfl

theorem serializer_entry (z : Resources p R Q hr hq (bound:=bound) x)
    (f : Forward z (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound))
    (hpre : z.base.pre=[]) :
    RecoveryBoundedGraphSerialize.Entry z.base.B z.circuit
      (Fin.addCases (m:=153) (n:=1506)
        (z.foldResult f.next [] f.refs
          (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).heads (fun _=>0))
      (Fin.addCases (m:=153) (n:=1506)
        (z.foldResult f.next [] f.refs
          (RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B)).tapes (fun _=>[])) := by
  let e:=RecoveryBoundedColdPrepared.extra R bound Q (Codec.clauses p).length z.base.B
  have hg:=z.circuit_graph e f hpre
  have ho:=z.circuit_reference e f
  have hw:=fold_retained_words z f.next f.refs
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    fin_cases j
    · have h : (z.foldResult f.next [] f.refs e).heads 20=
          ((z.foldResult f.next [] f.refs e).tapes 20).length := by
        apply RecoveryBoundedCountNativeFold.graph_head
      exact h.trans (congrArg List.length hg)
    · apply RecoveryBoundedCountNativeFold.output_head
    · exact fold_retained_heads z f.next f.refs 2
    · exact fold_retained_heads z f.next f.refs 3
    · exact fold_retained_heads z f.next f.refs 4
    · exact fold_retained_heads z f.next f.refs 5
    · rfl
  · intro j
    fin_cases j
    · exact hg
    · exact ho
    · exact congrFun hw 2
    · exact congrFun hw 3
    · exact congrFun hw 4
    · exact congrFun hw 5
    · rfl
  · intro j
    simp only [Fin.addCases_right]
  · intro j
    simp only [Fin.addCases_right]

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdCompile

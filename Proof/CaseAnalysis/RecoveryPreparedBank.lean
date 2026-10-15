import Proof.CaseAnalysis.RecoveryPreparedMeaning

/-! Identify the paid initial bank with the original count compiler's bank.
The graph, source tail, stack and candidate all begin at their literal zeros. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedCountUniform
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_empty (node B : ℕ) (out stack packet source : List Bool) :
    RecoveryBoundedGrammarBank.ready (fun _=>[]) node B out stack packet source=
      RecoveryBoundedGrammarBank.base node B out stack packet source := by
  funext i
  rw [RecoveryBoundedGrammarBank.ready,RecoveryBoundedRowReload.loaded_apply]
  fin_cases i <;> simp [RecoveryBoundedRowReload.ports,RecoveryBoundedGrammarBank.base,ZeroPadding.pad]

theorem extra_zero (q bound Q clauses B : ℕ) :
    extraAt B 0 (extra q bound Q clauses B)=extra q bound Q clauses B := by
  funext i
  by_cases hi : i=1
  · subst i
    simp [extraAt,extra,RecoveryBoundedColdMetadata.extra,RecoveryBoundedColdMetadata.extraValues]
  · simp only [extraAt,Function.update_of_ne hi]

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

theorem target_bank (z : Resources p R Q hr hq (bound:=bound) x)
    (hpre : z.base.pre=[]) (htail : z.base.sourceTail=[]) (hP : z.P=z.base.B) :
    (fun j : Fin 153=>targetData R bound (capacity z.base.W) Q (Codec.clauses p).length z.base.B
      (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) z.base.B)
      (DedupBytes.fields p) (j.castAdd 5))=
    scanData (z.bank (BooleanDAGBuilder.empty (descriptionWidth R bound)) 0 []
      (extra R bound Q (Codec.clauses p).length z.base.B)) bound := by
  simp only [targetData,Fin.addCases_left,Resources.bank,Resources.currentFields,
    Resources.currentPacket,extra_zero,RecoveryBoundedRows.Resources.word,
    BooleanDAGBuilder.empty,List.flatMap_nil,List.append_nil,hpre,htail,hP]
  simp only [ite_true,List.length_nil,ready_empty]
  rfl

theorem target_heads (z : Resources p R Q hr hq (bound:=bound) x) (hpre : z.base.pre=[]) :
    RecoveryBoundedColdPosition.positioned (fun _=>0)=
      Fin.addCases (m:=153) (n:=5)
        (scanHeads (z.heads (BooleanDAGBuilder.empty (descriptionWidth R bound)) []) 1) (fun _=>0) := by
  have hw : z.base.word (BooleanDAGBuilder.empty (descriptionWidth R bound))=[] := by
    simp only [RecoveryBoundedRows.Resources.word,BooleanDAGBuilder.empty,List.flatMap_nil,List.append_nil,hpre]
  unfold Resources.heads
  rw [hw]
  funext i
  fin_cases i <;> rfl

theorem extra_fields (q bound Q clauses B : ℕ) :
    extra q bound Q clauses B 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound) ∧
    extra q bound Q clauses B 3=RecoveryBoundedGrammarScalarAdd.unary B Q ∧
    extra q bound Q clauses B 4=RecoveryBoundedGrammarScalarAdd.unary B clauses ∧
    extra q bound Q clauses B 5=RecoveryBoundedGrammarScalarAdd.unary B (q+1) := by
  simp [extra,RecoveryBoundedColdMetadata.extra,RecoveryBoundedColdMetadata.extraValues]

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared

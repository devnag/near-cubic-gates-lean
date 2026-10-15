import Proof.Amplification.RecoveryClauseEvaluationTapes

/-! The bits read by the ordinary clause controller denote the same natural
literal tags and assignment values used in the all-code clause predicate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
open RepairSource.VerifierDecoding RecoveryValuationStream
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem checked_sign (s : State) (which : Fin 3) (word : List Bool) :
    (RecoveryCheckedLiteral.checkedState s which word).flag=decide ((Nat.unpair (value word)).1≠0) := by
  simp only [RecoveryCheckedLiteral.checkedState,RecoveryLiteralTag.nonzero,RecoveryCheckedLiteral.tagWord,
    (RecoveryFixedUnpair.word_values word).1]

theorem checked_tag (s : State) (which : Fin 3) (word : List Bool) :
    (RecoveryCheckedLiteral.checkedState s which word).result=decide ((Nat.unpair (value word)).1≤1) := by
  simp only [RecoveryCheckedLiteral.checkedState,RecoveryCheckedLiteral.tagWord,
    (RecoveryFixedUnpair.word_values word).1]

theorem checked_variable (s : State) (which : Fin 3) (word : List Bool) :
    (RecoveryCheckedLiteral.checkedState s which word).fields which=
      frame (RecoveryChildSelection.word false word) := by
  simp [RecoveryCheckedLiteral.checkedState,RecoveryLiteralDecode.decodedState]

theorem checked_field_other (s : State) (which j : Fin 3) (word : List Bool) (hj : j≠which) :
    (RecoveryCheckedLiteral.checkedState s which word).fields j=s.fields j := by
  simp [RecoveryCheckedLiteral.checkedState,RecoveryLiteralDecode.decodedState,hj]

theorem variable_value (word : List Bool) :
    value (RecoveryChildSelection.word false word)=(Nat.unpair (value word)).2 := by
  exact (RecoveryFixedUnpair.word_values word).2

theorem natural_literal_truth (assignment : Nat→Bool) (tag index : Nat) (ht : tag≤1) :
    RecoveryLiteralTruth.value (decide (tag≠0)) (assignment index)=
      TseitinCNF.literalEval assignment (RawSyntaxCertificate.projectLiteral (tag,index)) := by
  have he : tag=0 ∨ tag=1 := by omega
  rcases he with rfl|rfl <;>
    simp [RecoveryLiteralTruth.value,RawSyntaxCertificate.projectLiteral,TseitinCNF.literalEval]

theorem checked_truth (s : State) (e : Extra) (which : Fin 3) (word : List Bool)
    (table : FiniteValuation.Table)
    (ht : (RecoveryCheckedLiteral.checkedState s which word).result=true)
    (hv : e.value=FiniteValuation.assignment (value e.committed) (value e.binaryCount) table
      (Nat.unpair (value word)).2) :
    RecoveryLiteralTruth.value (RecoveryCheckedLiteral.checkedState s which word).flag e.value=
      TseitinCNF.literalEval (FiniteValuation.assignment (value e.committed) (value e.binaryCount) table)
        (RawSyntaxCertificate.projectLiteral (Nat.unpair (value word))) := by
  rw [checked_sign,hv]
  have htag : (Nat.unpair (value word)).1≤1 := by
    rw [checked_tag] at ht
    exact of_decide_eq_true ht
  exact natural_literal_truth _ _ _ htag

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation

import Proof.CaseAnalysis.RowsOriginalSchedule

/-! The grouped physical task schedule has the three original source-test
means, with no range promise on the guessed real proof. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open SourceInterfaces ComponentwiseValidity ComponentwiseBranchExtraction AggregateSemanticStage
open Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coordinates {n : ℕ} (p : TwoLiteralClause n) : Fin 2→Fin n:=![literalIndex p.left,literalIndex p.right]
theorem control_flag {n : ℕ} (S : ℕ) (p : TwoLiteralClause n) (side : Fin 2) :
    CloseoutRowsOriginalSourceTask.control S p (Fin.natAdd 2 side)=decide (S ≤ (coordinates p side).val) := by
  fin_cases side <;>rfl
noncomputable def prescribed {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (u : BitInput n) (p : TwoLiteralClause (pcpp.systematicBits+pcpp.auxiliaryBits)) (side : Fin 2) : ℝ:=
  bitAsReal ((systematicConstraint pcpp u (coordinates p side)).getD false)

theorem auxiliary_flag {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (u : BitInput n) (j : Fin (pcpp.systematicBits+pcpp.auxiliaryBits)) :
    decide (pcpp.systematicBits ≤ j.val)=(systematicConstraint pcpp u j).isNone := by
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [systematicConstraint,Fin.addCases_left,Fin.val_castAdd,Option.isNone_some]
    simp [show ¬pcpp.systematicBits ≤ k.val by omega]
  · intro k
    simp [systematicConstraint,Fin.val_natAdd]

noncomputable def pointwise {n : ℕ} {circuit : BooleanCircuit n} (phase : Phase) (pcpp : PointwisePCPP circuit)
    (v : BitInput n→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ) (u : BitInput n)
    (i : Fin (2^pcpp.clauseBits)) :=
  value phase (CloseoutRowsOriginalSourceTask.control pcpp.systematicBits (pcpp.clauses i))
    (fun side=>v u (coordinates (pcpp.clauses i) side)) (prescribed pcpp u (pcpp.clauses i))

theorem penalty_pointwise {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (v : BitInput n→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ) (u : BitInput n)
    (i : Fin (2^pcpp.clauseBits)) :
    pointwise .penalty pcpp v u i=
      validityPenalty (systematicConstraint pcpp u (literalIndex (pcpp.clauses i).left))
        (v u (literalIndex (pcpp.clauses i).left))+
      validityPenalty (systematicConstraint pcpp u (literalIndex (pcpp.clauses i).right))
        (v u (literalIndex (pcpp.clauses i).right)) := by
  apply penalty_value _ _ _ (fun side=>systematicConstraint pcpp u (coordinates (pcpp.clauses i) side))
  · intro side
    rw [control_flag]
    exact auxiliary_flag pcpp u (coordinates (pcpp.clauses i) side)
  · intro side b hb;simp [prescribed,hb]

noncomputable def mean {n : ℕ} {circuit : BooleanCircuit n} (phase : Phase) (pcpp : PointwisePCPP circuit)
    (v : BitInput n→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ) : ℝ:=
  (𝔼 slot : BitInput n×Fin (2^pcpp.clauseBits),pointwise phase pcpp v slot.1 slot.2)/(divisor phase : ℝ)

theorem penalty_mean {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (v : BitInput n→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ) :
    mean .penalty pcpp v=aggregateClausePenaltyMean pcpp v/2 := by
  unfold mean
  simp_rw [penalty_pointwise]
  congr 1
  rw [←Finset.univ_product_univ,Finset.expect_product]
  simp only [aggregateClausePenaltyMean,totalClausePenaltyMean,clausePenaltyMean,Finset.expect_add_distrib]

theorem moment_mean {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (v : BitInput n→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ) :
    mean .moment pcpp v=CompetitorSourceAverage.leftSecondMoment pcpp v := by
  simp only [mean,pointwise,moment_value,divisor,Nat.cast_one,div_one,coordinates,
    Matrix.cons_val_zero,CompetitorSourceAverage.leftSecondMoment]

theorem clause_mean {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (v : BitInput n→Fin (pcpp.systematicBits+pcpp.auxiliaryBits)→ℝ) :
    mean .clause pcpp v=aggregateClauseMean pcpp v := by
  rw [aggregateClauseMean_eq_joint]
  simp only [mean,pointwise,clause_value,divisor,Nat.cast_one,div_one,
    CloseoutRowsOriginalSourceTask.control,CloseoutRowsOriginalClause.negative,coordinates,
    Matrix.cons_val_zero,Matrix.cons_val_one,clauseRealValue]

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule

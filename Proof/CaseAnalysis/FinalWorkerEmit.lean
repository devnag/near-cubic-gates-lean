import Proof.CaseAnalysis.FinalWorkerJoin
import Proof.CaseAnalysis.RowsEstimatorCoefficientsAppend

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **One AND-four supplier call, emitted as one record word.**  The run is
real, its cost depends only on the scalar width -- never on the witness length
-- and the two conjuncts at the end say what the emitted operands mean: the
monomial's rational coefficient, and the supplier's answer to that monomial's
factor list, which has at most four entries by
`Calls.factors_length_le_four`. -/
theorem call_record_run {Atom : Type} {supplier : List Atom → ℚ}
    {monomial : CircuitMonomial Atom 4} {entry : Entry} (recordWidth : ℕ)
    (hcall : Calls supplier monomial entry) :
    ∃ receipt,
      run CompetitorCountRecordAppend.machine
          (CompetitorCountRecordAppend.budget recordWidth)
          (CloseoutRowsEstimatorCoefficients.Append.input recordWidth entry.coefficient entry.count entry.denominator) =
        some receipt ∧
      receipt.steps ≤ CompetitorCountRecordAppend.budget recordWidth ∧
      receipt.final.tapes 28 =
        CloseoutRowsEstimatorCoefficients.Stream.entryWord recordWidth entry ∧
      entry.coefficient.value = monomial.coefficient ∧
      ((entry.count : ℚ) / (entry.denominator : ℚ)) = supplier monomial.factors ∧
      monomial.factors.length ≤ 4 := by
  obtain ⟨receipt, hrun, hsteps, hword, _hheads, _hdriver, _hcount⟩ :=
    CloseoutRowsEstimatorCoefficients.Append.record_run recordWidth entry.coefficient entry.count entry.denominator
  exact ⟨receipt, hrun, hsteps, hword, hcall.coefficient, hcall.answer,
    Calls.factors_length_le_four hcall⟩

theorem result_record_run (width : ℕ) (estimate : CompetitorValidity.Estimate) :
    ∃ receipt,
      run CompetitorCountRecordAppend.machine
          (CompetitorCountRecordAppend.budget width)
          (CloseoutRowsEstimatorCoefficients.Append.input width estimate 1 1) = some receipt ∧
      receipt.steps ≤ CompetitorCountRecordAppend.budget width ∧
      receipt.final.tapes 28 =
        CloseoutRowsEstimatorCoefficients.Stream.recordWord width estimate 1 1 := by
  obtain ⟨receipt, hrun, hsteps, hword, _hheads, _hdriver, _hcount⟩ :=
    CloseoutRowsEstimatorCoefficients.Append.record_run width estimate 1 1
  exact ⟨receipt, hrun, hsteps, hword⟩

theorem estimate_record_run {Atom : Type} (supplier : List Atom → ℚ)
    (recordWidth width : ℕ) (polynomial : CircuitPolynomial Atom 4)
    (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hvalid : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate recordWidth) :
    ∃ receipt,
      run CompetitorCountRecordAppend.machine
          (CompetitorCountRecordAppend.budget width)
          (CloseoutRowsEstimatorCoefficients.Append.input width (CompetitorSumFold.folded CompetitorSumWidth.zero
            (contributions entries)) 1 1) = some receipt ∧
      receipt.steps ≤ CompetitorCountRecordAppend.budget width ∧
      receipt.final.tapes 28 =
        CloseoutRowsEstimatorCoefficients.Stream.recordWord width
          (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
          1 1 ∧
      (((CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions entries)).value : ℚ) : ℝ) =
        polynomial.estimatedMean supplier := by
  obtain ⟨receipt, hrun, hsteps, hword⟩ :=
    result_record_run width
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
  exact ⟨receipt, hrun, hsteps, hword,
    folded_value_eq_estimatedMean supplier recordWidth polynomial entries hcalls hvalid⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit

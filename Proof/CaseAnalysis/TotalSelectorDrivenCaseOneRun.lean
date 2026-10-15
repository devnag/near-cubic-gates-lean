import Proof.Circuits.InverseTotalScheduledRowStageClosure
import Proof.Circuits.SelectorDrivenRegisterTargetChainBase
import Proof.Circuits.UniformTargetTotalRun

/-! # Total direct selector Case-one chain -/

namespace NearCubicWires.TotalSelectorDrivenCaseOneRun

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseTotalScheduledRowStageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.UniformTargetTotalRun
open NearCubicWires.VerifiedLinker

set_option maxRecDepth 2000 in
-- The scheduled bank frame and amplifier request are deeply paired values.
set_option maxHeartbeats 1600000 in
-- The bank-register resources normalize the full scheduled amplifier request.
/-- The concrete guarded row stage makes the direct selector Case-one program
halt with a Boolean on every selector-frame request. -/
theorem totalBooleanRuns_inverseSelectorCaseOneProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ) :
    TotalBooleanRuns
      (inverseSelectorCaseOneProgram contracts clockDepth machine
        (inverseTotalScheduledRowProgram contracts clockDepth))
      (inverseSelectorDirectChainBits contracts clockDepth machine
        advantageExponent
        (inverseTotalScheduledRowBits contracts clockDepth machine
          advantageExponent)
        occurrenceBits)
      (inverseSelectorDirectChainFuel contracts clockDepth machine
        advantageExponent
        (inverseTotalScheduledRowProgram contracts clockDepth) occurrence
        (inverseTotalScheduledRowFuel contracts clockDepth machine
          advantageExponent)
        occurrenceFuel)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent) := by
  intro request
  let algorithm := (publishedAmplifier contracts).algorithm
  let amplifierRequest :=
    inverseChainAmplifierRequest contracts clockDepth machine
      advantageExponent request.length
  let outputArity := algorithm.outputArity amplifierRequest
  let descriptor := algorithm.descriptor amplifierRequest
  let value :=
    ((decide
      (algorithm.evaluator.execute
        (paddedAmplifierEvaluationRequest outputArity descriptor request.code) ≠
          0) : Bool).toNat)
  have hvalue : value ≤ 1 := by
    unfold value
    cases decide
      (algorithm.evaluator.execute
          (paddedAmplifierEvaluationRequest outputArity descriptor
            request.code) ≠ 0) <;>
      simp
  refine ⟨value, hvalue, ?_⟩
  have hrun :=
    run_bankRegisterCaseOneTargetBitProgram algorithm
      (inverseTotalScheduledRowProgram contracts clockDepth)
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
        advantageExponent
        request.length)
      request.length
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent
          request.length))
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent
            request.length)))
      (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent
          request.length))
      request.code
      (targetBitCaseOneBits algorithm request.length
        outputArity descriptor request.code)
      (targetBitCaseOneFuel algorithm
        outputArity descriptor request.code)
      value
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent request.length)
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent request.length)
      (fun code _hcode =>
        run_inverseTotalScheduledRowProgram contracts clockDepth machine
          advantageExponent request.length code)
      (run_targetBitProgram_caseOne algorithm request.length
        outputArity descriptor request.code)
  unfold inverseSelectorCaseOneProgram inverseSelectorDirectChainBits
    inverseSelectorDirectChainFuel inverseSelectorAdapterFrame
  rw [selectorDrivenBankFrame_eq]
  exact run_fuel_mono
    (run_bits_mono hrun (Nat.le_max_left _ _))
    (Nat.le_max_left _ _)

end NearCubicWires.TotalSelectorDrivenCaseOneRun

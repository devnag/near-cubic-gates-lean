import Proof.Circuits.TotalSelectorDrivenContextContracts

/-! # Raw all-request selector atom-context pipeline -/

namespace NearCubicWires.TotalSelectorDrivenContextPipeline

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.TotalSelectorDrivenAdapterContracts
open NearCubicWires.UniformTargetLanguageBank

open private run_contextDuplicateProgram run_contextSwapProgram
  from Proof.MachineModel.BankAtomContextRegisters

set_option maxHeartbeats 1600000 in
-- The nested linker trace normalizes three dependent selector-frame ledgers.
/-- The raw duplicate/numeral/swap/table register pipeline, before the
presentation theorem identifies its paired registers with `inverseAtomContext`.
-/
theorem run_totalInverseSelectorAtomContextProgram_ofTable
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ)
    (htable :
      TotalInverseSelectorAtomTableRuns contracts clockDepth machine
        advantageExponent pcp table tableBits tableFuel)
    (request : LanguageEvaluationRequest) :
    runNPOracleProgram
        (inverseAtomContextProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          table)
        (inverseSelectorAtomContextBits contracts clockDepth machine
          advantageExponent pcp tableBits request)
        (inverseAtomContextFuel contracts advantageExponent table tableFuel
          request)
        (initialNPOracleState request.length
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)) =
      some
        (Nat.pair
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent request.length)))
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSelectorBankWidth contracts clockDepth advantageExponent
                request.length))
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              request.length)
            (inverseSelectorBankQueryCount contracts clockDepth
              advantageExponent request.length))) := by
  exact run_occurrenceStage
    (run_contextDuplicateProgram request.length
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request))
    (run_occurrenceStage
      (run_preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        request.length _ _
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          request)
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          request)
        _
        (run_bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          request.length
          (inverseScheduleLength contracts clockDepth advantageExponent
            request.length)
          (inverseSelectorBankWidth contracts clockDepth advantageExponent
            request.length)
          (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
            request.length)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              request.length))
          (encodeBitInput request.input)))
      (run_occurrenceStage
        (run_contextSwapProgram request.length _
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request))
        (run_preserveRightProgram table request.length (tableBits request)
          (tableFuel request)
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)
          _ _ (htable request))))

end NearCubicWires.TotalSelectorDrivenContextPipeline

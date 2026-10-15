import Proof.PCP.SelectorDrivenProjectionTableStage

/-! # All-request selector adapter contracts -/

namespace NearCubicWires.TotalSelectorDrivenAdapterContracts

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns

def TotalInverseSelectorAtomTableRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest,
    runNPOracleProgram table (tableBits request) (tableFuel request)
        (initialNPOracleState request.length
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              request.length)))

end NearCubicWires.TotalSelectorDrivenAdapterContracts

import Proof.Circuits.SelectorDrivenBodyDispatch

/-! # Exact scheduled resources for the selector-frame branch selector -/

namespace NearCubicWires.TotalSelectorDrivenSelectorResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyDispatch

theorem inverseBankSelectorBitsAtFrame_eq_schedule
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (frame emitterBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) :
    inverseBankSelectorBitsAtFrame contracts clockDepth machine
        advantageExponent frame emitterBits request =
      emittedBranchSelectorBits
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          request.length)
        (inverseScheduleBound contracts clockDepth advantageExponent
          request.length)
        request.length (frame request) (emitterBits request) := by
  rfl

theorem inverseBankSelectorFuel_eq_schedule
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitterFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) :
    inverseBankSelectorFuel contracts clockDepth machine advantageExponent
        emitterFuel request =
      emittedBranchSelectorFuel
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          request.length)
        (inverseScheduleBound contracts clockDepth advantageExponent
          request.length)
        (emitterFuel request) := by
  rfl

end NearCubicWires.TotalSelectorDrivenSelectorResources

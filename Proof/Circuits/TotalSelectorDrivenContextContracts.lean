import Proof.Circuits.TotalSelectorDrivenAdapterRuns

/-! # All-request selector context, shape, and frame-adapter contracts -/

namespace NearCubicWires.TotalSelectorDrivenContextContracts

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns

def TotalInverseSelectorAtomContextRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest,
    runNPOracleProgram context (contextBits request) (contextFuel request)
        (initialNPOracleState request.length
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)) =
      some
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          request.length)

def TotalInverseSelectorAtomShapeRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest,
    runNPOracleProgram shape (shapeBits request) (shapeFuel request)
        (initialNPOracleState request.length
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)) =
      some
        (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
          request)

def TotalInverseSelectorFrameAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest,
    runNPOracleProgram adapter (adapterBits request) (adapterFuel request)
        (initialNPOracleState request.length
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)) =
      some
        (Nat.pair
          (generatedBalancedRangeInput
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              request.length)
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp request.length))
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request))

end NearCubicWires.TotalSelectorDrivenContextContracts

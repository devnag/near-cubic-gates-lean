import Proof.Circuits.TotalSelectorDrivenShapeRuns

/-! # All-request selector frame-adapter run -/

namespace NearCubicWires.TotalSelectorDrivenFrameRuns

open NearCubicWires
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.TotalSelectorDrivenContextContracts

open private run_frameDuplicateProgram
  from Proof.MachineModel.BankFrameLoweringAdapter

/-- Frame duplication and right-preservation are total transducers, so a total
selector shape yields a total retained-frame adapter. -/
theorem totalInverseSelectorFrameAdapterRuns_ofShape
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ)
    (hshape :
      TotalInverseSelectorAtomShapeRuns contracts clockDepth machine
        advantageExponent pcp shape shapeBits shapeFuel) :
    TotalInverseSelectorFrameAdapterRuns contracts clockDepth machine
      advantageExponent pcp (inverseFrameAdapterProgram shape)
      (inverseSelectorFrameAdapterBits contracts clockDepth machine
        advantageExponent pcp shapeBits)
      (inverseFrameAdapterFuel shape shapeFuel) := by
  intro request
  exact run_occurrenceStage
    (run_frameDuplicateProgram request.length
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request))
    (run_preserveRightProgram shape request.length (shapeBits request)
      (shapeFuel request)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
        request)
      (hshape request))

end NearCubicWires.TotalSelectorDrivenFrameRuns

import Proof.Circuits.TotalSelectorDrivenContextRuns
import Proof.MachineModel.TotalSelectorAtomShapeProgram

/-! # Total selector atom-shape count tail -/

namespace NearCubicWires.TotalSelectorDrivenShapeTail

open NearCubicWires
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalSelectorAtomShapeProgram

/-- The guarded formula-length call at index `0`, paired with the already
computed selector atom context.  This theorem is independent of the outer
context program and is valid at request length zero. -/
theorem run_totalInverseSelectorAtomShapeTail
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcompiler :
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel)
    (request : LanguageEvaluationRequest) :
    runNPOracleProgram totalAtomShapeCountProgram
        (atomShapeCountBits request.length
          (inverseAtomContext contracts clockDepth machine advantageExponent
            pcp request.length)
          (structuralAtomCountBits request.length
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent request.length))
            (pcp.nativeWidth
              (inverseScheduleLength contracts clockDepth advantageExponent
                request.length))
            (pcp.queryCount
              (inverseScheduleLength contracts clockDepth advantageExponent
                request.length))
            (inverseScheduleBound contracts clockDepth advantageExponent
              request.length)
            0 (compilerBits request.length 0))
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            request.length))
        (totalAtomShapeCountFuel
          (structuralAtomCountFuelFor totalSelectiveCountCasesProgram
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent request.length))
            (pcp.nativeWidth
              (inverseScheduleLength contracts clockDepth advantageExponent
                request.length))
            (pcp.queryCount
              (inverseScheduleLength contracts clockDepth advantageExponent
                request.length))
            (inverseScheduleBound contracts clockDepth advantageExponent
              request.length)
            0 (compilerFuel request.length 0)))
        (initialNPOracleState request.length
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            request.length)) =
      some
        (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
          request) := by
  exact run_totalAtomShapeCountProgram request.length
    (inverseAtomContext contracts clockDepth machine advantageExponent pcp
      request.length)
    _ _
    (inverseAtomCount contracts clockDepth machine advantageExponent pcp
      request.length)
    (run_totalStructuralAtomCountProgram_index pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        request.length)
      request.length
      (inverseScheduleBound contracts clockDepth advantageExponent
        request.length)
      (compilerBits request.length 0) (compilerFuel request.length 0)
      (hcompiler request.length 0
        (inverseAtomCount_pos contracts clockDepth machine advantageExponent pcp
          request.length)))

end NearCubicWires.TotalSelectorDrivenShapeTail

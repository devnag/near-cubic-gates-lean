import Proof.Circuits.SelectorDrivenAtomContextRuns
import Proof.Circuits.TotalInverseCompilerRuns
import Proof.MachineModel.TotalStructuralFormulaProgram

/-!
# The guarded atom-count shape stage at the selector frame

The selector adapter computes the structural atom count at index `0`.  This
module rebuilds only that count tail around the total compiler and preserves
the existing selector context and frame contracts.
-/

namespace NearCubicWires.TotalSelectorAtomShapeProgram

open NearCubicWires
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalStructuralAtomCalleeProgram
open NearCubicWires.VerifiedLinker

open private atomContextRequestBits atomContextRequestProgram
  natBitLength_mono' run_atomContextRequestProgram from
    Proof.MachineModel.BankAtomShapeCountStage

/-! ## 1. The count projection with compiler ownership exposed -/

def structuralAtomCountProgramFor
  (compilerProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (structuralFormulaProgramFor compilerProgram)
    BankAtomShapeCountStage.structuralAtomTakeLeftProgram

def structuralAtomCountFuelFor (compilerProgram : NPOracleProgram)
    (outputs : List ℕ) (width count bound index compilerFuel : ℕ) : ℕ :=
  linkFuel BankAtomShapeCountStage.structuralAtomTakeLeftProgram
    (structuralFormulaPipelineFuelFor compilerProgram
      outputs width count bound index compilerFuel)
    2

theorem run_structuralAtomCountProgramFor
    (compilerProgram : NPOracleProgram)
    (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits compilerFuel : ℕ)
    (hcompiler :
      runNPOracleProgram compilerProgram compilerBits compilerFuel
          (initialNPOracleState machineInputLength <|
            structuralCompilerCoreInput outputs width count bound index) =
        some
          (selectiveWireCode
            (selectiveCompileTableBoundedOracleVerifier outputs width count
              bound (index - descriptionWidth width bound)))) :
    runNPOracleProgram (structuralAtomCountProgramFor compilerProgram)
        (structuralAtomCountBits machineInputLength outputs width count bound
          index compilerBits)
        (structuralAtomCountFuelFor compilerProgram outputs width count bound
          index compilerFuel)
        (initialNPOracleState machineInputLength
          (structuralFormulaRequestCode outputs width count bound index)) =
      some
        (tableBoundedOracleStructuralFormulaLength
          outputs width count bound) := by
  refine run_occurrenceStage
    (run_structuralFormulaProgramFor compilerProgram machineInputLength outputs
      width count bound index compilerBits compilerFuel hcompiler) ?_
  exact BankAtomShapeCountStage.run_structuralAtomTakeLeftProgram
    machineInputLength
    (tableBoundedOracleStructuralFormulaLength outputs width count bound)
    (tableBoundedOracleStructuralFormulaAtomAt outputs width count bound index)
    (natBitLength_mono' (Nat.left_le_pair _ _))

def totalStructuralAtomCountProgram : NPOracleProgram :=
  structuralAtomCountProgramFor totalSelectiveCountCasesProgram

theorem run_totalStructuralAtomCountProgram_index
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (machineInputLength bound compilerBits compilerFuel : ℕ)
    (hcompiler :
      StructuralCompilerProgramRunsAt totalSelectiveCountCasesProgram pcp input
        machineInputLength bound 0 compilerBits compilerFuel) :
    runNPOracleProgram totalStructuralAtomCountProgram
        (structuralAtomCountBits machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound 0 compilerBits)
        (structuralAtomCountFuelFor totalSelectiveCountCasesProgram
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound 0 compilerFuel)
        (initialNPOracleState machineInputLength
          (Nat.pair 0 (structuralAtomContext pcp input bound))) =
      some (structuralAtomCount pcp input bound) :=
  run_structuralAtomCountProgramFor totalSelectiveCountCasesProgram
    machineInputLength (projectionRunnerCallOutputs pcp input)
    (pcp.nativeWidth n) (pcp.queryCount n) bound 0 compilerBits compilerFuel
    hcompiler

/-! ## 2. The guarded count-and-pair stage -/

def totalAtomShapeCountProgram : NPOracleProgram :=
  linkPrograms atomContextRequestProgram
    (preserveRightProgram totalStructuralAtomCountProgram)

def totalAtomShapeCountFuel (countFuel : ℕ) : ℕ :=
  linkFuel (preserveRightProgram totalStructuralAtomCountProgram) 4
    (preserveRightFuel countFuel)

theorem run_totalAtomShapeCountProgram
    (machineInputLength context countBits countFuel count : ℕ)
    (hcount :
      runNPOracleProgram totalStructuralAtomCountProgram countBits countFuel
          (initialNPOracleState machineInputLength (Nat.pair 0 context)) =
        some count) :
    runNPOracleProgram totalAtomShapeCountProgram
        (atomShapeCountBits machineInputLength context countBits count)
        (totalAtomShapeCountFuel countFuel)
        (initialNPOracleState machineInputLength context) =
      some (generatedBalancedRangeInput count context) :=
  run_occurrenceStage
    (run_atomContextRequestProgram machineInputLength context)
    (run_preserveRightProgram totalStructuralAtomCountProgram machineInputLength
      countBits countFuel (Nat.pair 0 context) context count hcount)

/-! ## 3. The selector-frame shape supplier -/

def totalInverseAtomShapeProgram (context : NPOracleProgram) : NPOracleProgram :=
  linkPrograms context totalAtomShapeCountProgram

noncomputable def totalInverseAtomShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (contextFuel : LanguageEvaluationRequest → ℕ)
    (compilerFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel totalAtomShapeCountProgram (contextFuel request)
    (totalAtomShapeCountFuel
      (structuralAtomCountFuelFor totalSelectiveCountCasesProgram
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (inverseScheduleBound contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request))
        0 (compilerFuel (LanguageEvaluationRequest.length request) 0)))

theorem totalInverseSelectorAtomShapeRuns_ofContext
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcontext :
      InverseSelectorAtomContextRuns contracts clockDepth machine
        advantageExponent pcp context contextBits contextFuel)
    (hcompiler :
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel) :
    InverseSelectorAtomShapeRuns contracts clockDepth machine advantageExponent
      pcp (totalInverseAtomShapeProgram context)
      (inverseAtomShapeBits contracts clockDepth machine advantageExponent pcp
        contextBits compilerBits)
      (totalInverseAtomShapeFuel contracts clockDepth machine advantageExponent
        pcp contextFuel compilerFuel) := by
  intro target hlarge input
  exact run_occurrenceStage (hcontext target hlarge input)
    (run_totalAtomShapeCountProgram target
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target)
      _ _
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target)
      (run_totalStructuralAtomCountProgram_index pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target)
        target (inverseScheduleBound contracts clockDepth advantageExponent
          target)
        (compilerBits target 0) (compilerFuel target 0)
        (hcompiler target 0
          (inverseAtomCount_pos contracts clockDepth machine advantageExponent
            pcp target))))

end NearCubicWires.TotalSelectorAtomShapeProgram

import Proof.MachineModel.TotalStructuralFormulaProgram

/-!
# The guarded structural atom callee

This is the direct two-instruction projection wrapper around the
program-parametric structural formula stream.
-/

namespace NearCubicWires.TotalStructuralAtomCalleeProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.VerifiedLinker

/-- The pointwise structural atom callee with compiler ownership exposed. -/
def structuralAtomCalleeProgramFor
    (compilerProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (structuralFormulaProgramFor compilerProgram)
    structuralAtomTakeRightProgram

/-- Fuel of the pointwise atom callee with a program-parametric compiler. -/
def structuralAtomCalleeFuelFor (compilerProgram : NPOracleProgram)
    (outputs : List ℕ) (width count bound index compilerFuel : ℕ) : ℕ :=
  linkFuel structuralAtomTakeRightProgram
    (structuralFormulaPipelineFuelFor compilerProgram
      outputs width count bound index compilerFuel)
    2

theorem run_structuralAtomCalleeProgramFor
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
    runNPOracleProgram (structuralAtomCalleeProgramFor compilerProgram)
        (structuralAtomCalleeBits machineInputLength outputs width count bound
          index compilerBits)
        (structuralAtomCalleeFuelFor compilerProgram outputs width count bound
          index compilerFuel)
        (initialNPOracleState machineInputLength
          (structuralFormulaRequestCode outputs width count bound index)) =
      some
        (tableBoundedOracleStructuralFormulaAtomAt
          outputs width count bound index) := by
  refine run_occurrenceStage
    (run_structuralFormulaProgramFor compilerProgram machineInputLength outputs
      width count bound index compilerBits compilerFuel hcompiler) ?_
  exact run_structuralAtomTakeRightProgram machineInputLength
    (tableBoundedOracleStructuralFormulaLength outputs width count bound)
    (tableBoundedOracleStructuralFormulaAtomAt outputs width count bound index)
    (natBitLength_mono (Nat.right_le_pair _ _))

/-- The guarded concrete compiler installed in the direct atom callee. -/
def totalStructuralAtomCalleeProgram : NPOracleProgram :=
  structuralAtomCalleeProgramFor totalSelectiveCountCasesProgram

def totalStructuralAtomCalleeRequestFuel
    (outputs : List ℕ) (width count bound : ℕ)
    (compilerFuel : ℕ → ℕ) (request : ℕ) : ℕ :=
  structuralAtomCalleeFuelFor totalSelectiveCountCasesProgram
    outputs width count bound (structuralAtomRequestIndex request)
    (compilerFuel (structuralAtomRequestIndex request))

/-- The exact direct-body wrapper, from the guarded compiler contract. -/
theorem run_totalStructuralAtomCalleeProgram_index
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (machineInputLength bound index compilerBits : ℕ)
    (compilerFuel : ℕ → ℕ)
    (hcompiler :
      StructuralCompilerProgramRunsAt totalSelectiveCountCasesProgram
        pcp input machineInputLength bound index compilerBits
        (compilerFuel index)) :
    runNPOracleProgram totalStructuralAtomCalleeProgram
        (structuralAtomCalleeBits machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound index compilerBits)
        (totalStructuralAtomCalleeRequestFuel
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound compilerFuel
          (balancedRangeRequestAtom machineInputLength index
            (structuralAtomContext pcp input bound)))
        (initialNPOracleState machineInputLength
          (Nat.pair index (structuralAtomContext pcp input bound))) =
      some (structuralAtomValue pcp input bound index) := by
  have hindex :
      structuralAtomRequestIndex
          (balancedRangeRequestAtom machineInputLength index
            (structuralAtomContext pcp input bound)) =
        index :=
    structuralAtomRequestIndex_atom machineInputLength index
      (structuralAtomContext pcp input bound)
  rw [totalStructuralAtomCalleeRequestFuel, hindex]
  exact run_structuralAtomCalleeProgramFor totalSelectiveCountCasesProgram
    machineInputLength (projectionRunnerCallOutputs pcp input)
    (pcp.nativeWidth n) (pcp.queryCount n) bound index compilerBits
    (compilerFuel index) hcompiler

end NearCubicWires.TotalStructuralAtomCalleeProgram

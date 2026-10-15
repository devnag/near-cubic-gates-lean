import Proof.MachineModel.TotalStructuralAtomCalleeProgram

/-!
# The structural atom emitter's callee/program contract

This module isolates the exact pointwise proposition consumed by the guarded
emitter.  It contains no emitter bytecode.
-/

namespace NearCubicWires.TotalStructuralAtomEmitterProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalStructuralAtomCalleeProgram

/-- A pointwise structural-atom callee tied to the compiler program whose run
justifies it.  The contract uses the callee's own width; the emitter separately
widens that run to its shared range width. -/
def StructuralAtomCalleeEmitterContract
    (compilerProgram calleeProgram : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound : ℕ)
    (compilerBits compilerFuel : ℕ → ℕ) (calleeFuel : ℕ → ℕ) : Prop :=
  ∀ index, index < structuralAtomCount pcp input bound →
    StructuralCompilerProgramRunsAt compilerProgram pcp input
        machineInputLength bound index (compilerBits index)
        (compilerFuel index) →
      runNPOracleProgram calleeProgram
          (structuralAtomCalleeBits machineInputLength
            (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
            (pcp.queryCount n) bound index (compilerBits index))
          (calleeFuel
            (balancedRangeRequestAtom machineInputLength index
              (structuralAtomContext pcp input bound)))
          (initialNPOracleState machineInputLength
            (Nat.pair index (structuralAtomContext pcp input bound))) =
        some (structuralAtomValue pcp input bound index)

/-- The frozen guarded callee supplies the exact emitter contract. -/
theorem totalStructuralAtomCalleeEmitterContract
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound : ℕ)
    (compilerBits compilerFuel : ℕ → ℕ) :
    StructuralAtomCalleeEmitterContract totalSelectiveCountCasesProgram
      totalStructuralAtomCalleeProgram pcp input machineInputLength bound
      compilerBits compilerFuel
      (totalStructuralAtomCalleeRequestFuel
        (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
        (pcp.queryCount n) bound compilerFuel) := by
  intro index _ hcompiler
  exact run_totalStructuralAtomCalleeProgram_index pcp input
    machineInputLength bound index (compilerBits index) compilerFuel hcompiler

end NearCubicWires.TotalStructuralAtomEmitterProgram

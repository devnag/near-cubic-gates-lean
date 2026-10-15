import Proof.Circuits.InverseDescriptionAtomStream
import Proof.MachineModel.TotalStructuralAtomCalleeProgram

/-!
# The guarded balanced structural atom range

This is the balanced-list twin of the total tagged emitter.  It installs the
guarded pointwise callee without changing the generated range request or
balanced atom-list output.
-/

namespace NearCubicWires.TotalStructuralAtomRangeProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseDescriptionAtomStream
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalStructuralAtomCalleeProgram
open NearCubicWires.VerifiedLinker

set_option maxHeartbeats 800000 in
-- The guarded callee request fuel is a full concrete linker term.
theorem run_totalStructuralAtomRangeProgram_ofCompiler
    {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound : ℕ)
    (compilerBits compilerFuel : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength machineInputLength ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) ≤
        rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms machineInputLength
              (structuralAtomContext pcp input bound) 0
              (structuralAtomCount pcp input bound))) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp input bound
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms machineInputLength
            (structuralAtomContext pcp input bound) 0
            (structuralAtomCount pcp input bound)) ≤
        rangeBits)
    (hcalleeBits : ∀ index, index < structuralAtomCount pcp input bound →
      structuralAtomCalleeBits machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound index (compilerBits index) ≤
        rangeBits)
    (hcompiler : ∀ index, index < structuralAtomCount pcp input bound →
      StructuralCompilerProgramRunsAt totalSelectiveCountCasesProgram
        pcp input machineInputLength bound index (compilerBits index)
        (compilerFuel index)) :
    runNPOracleProgram
        (structuralAtomRangeProgram totalStructuralAtomCalleeProgram)
        rangeBits
        (structuralAtomRangeFuel totalStructuralAtomCalleeProgram
          machineInputLength (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound)
          (totalStructuralAtomCalleeRequestFuel
            (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
            (pcp.queryCount n) bound compilerFuel))
        (initialNPOracleState machineInputLength
          (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound))) =
      some
        (encodeBalancedList
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)) := by
  refine run_structuralAtomRangeProgram_table_at
    totalStructuralAtomCalleeProgram pcp input machineInputLength bound _
    hpositive hlengthBits hrangeBits hlistBits hcallBits ?_
  intro index hindex
  exact run_bits_mono
    (run_totalStructuralAtomCalleeProgram_index pcp input machineInputLength
      bound index (compilerBits index) compilerFuel
      (hcompiler index hindex))
    (hcalleeBits index hindex)

end NearCubicWires.TotalStructuralAtomRangeProgram

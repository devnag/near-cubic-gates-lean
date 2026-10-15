import Proof.MachineModel.StructuralAtomEmitterProgramContract

/-!
# The guarded structural atom emitter

This module parameterizes exactly the emitter boundary that previously fixed
both the old structural-atom callee and the old compiler proposition.  The
range loop, request ABI, bit ledger, atom list, and retained point code are
unchanged.
-/

namespace NearCubicWires.TotalStructuralAtomEmitterProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
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
open NearCubicWires.VerifiedLinker

/-! ## 1. The program-parametric emitter boundary -/

/-- The old `run_structuralAtomEmitterProgram_ofCompiler` with executable
ownership exposed through `StructuralAtomCalleeEmitterContract`. -/
theorem run_structuralAtomEmitterProgram_ofCalleeContract
    (compilerProgram calleeProgram : NPOracleProgram)
    {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound pointCode : ℕ)
    (compilerBits compilerFuel : ℕ → ℕ) (calleeFuel : ℕ → ℕ)
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
      StructuralCompilerProgramRunsAt compilerProgram pcp input
        machineInputLength bound index (compilerBits index)
        (compilerFuel index))
    (hcallee :
      StructuralAtomCalleeEmitterContract compilerProgram calleeProgram
        pcp input machineInputLength bound compilerBits compilerFuel
        calleeFuel) :
    runNPOracleProgram (structuralAtomEmitterProgram calleeProgram)
        (structuralAtomEmitterBits rangeBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) pointCode
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (structuralAtomEmitterFuel calleeProgram machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) calleeFuel
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (initialNPOracleState machineInputLength
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodeTaggedList
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
          pointCode) := by
  refine run_structuralAtomEmitterProgram_table_at calleeProgram pcp input
    machineInputLength bound pointCode calleeFuel hpositive hlengthBits
    hrangeBits hlistBits hcallBits ?_
  intro index hindex
  exact run_bits_mono
    (hcallee index hindex (hcompiler index hindex))
    (hcalleeBits index hindex)

/-! ## 2. The concrete guarded emitter and its preserved ABI -/

/-- The structural atom emitter with the guarded pointwise callee installed. -/
def totalStructuralAtomEmitterProgram : NPOracleProgram :=
  structuralAtomEmitterProgram totalStructuralAtomCalleeProgram

/-- The unchanged emitter width ledger, exported under the guarded name. -/
def totalStructuralAtomEmitterBits
    (rangeBits inputLength count context pointCode : ℕ) (atoms : List ℕ) : ℕ :=
  structuralAtomEmitterBits rangeBits inputLength count context pointCode atoms

/-- The unchanged emitter fuel ledger, with the guarded callee installed. -/
def totalStructuralAtomEmitterFuel
    (inputLength count context : ℕ) (calleeFuel : ℕ → ℕ)
    (atoms : List ℕ) : ℕ :=
  structuralAtomEmitterFuel totalStructuralAtomCalleeProgram
    inputLength count context calleeFuel atoms

/-- **The guarded structural atom emitter from compiler runs alone.**  This
has the same input and output ABI and the same resource arguments as the old
emitter theorem; only the compiler proposition names the guarded program. -/
theorem run_totalStructuralAtomEmitterProgram_ofCompiler
    {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound pointCode : ℕ)
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
    runNPOracleProgram totalStructuralAtomEmitterProgram
        (totalStructuralAtomEmitterBits rangeBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) pointCode
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (totalStructuralAtomEmitterFuel machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound)
          (totalStructuralAtomCalleeRequestFuel
            (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
            (pcp.queryCount n) bound compilerFuel)
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (initialNPOracleState machineInputLength
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodeTaggedList
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
          pointCode) := by
  exact run_structuralAtomEmitterProgram_ofCalleeContract
    totalSelectiveCountCasesProgram totalStructuralAtomCalleeProgram pcp input
    machineInputLength bound pointCode compilerBits compilerFuel
    (totalStructuralAtomCalleeRequestFuel
      (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
      (pcp.queryCount n) bound compilerFuel)
    hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits hcompiler
    (totalStructuralAtomCalleeEmitterContract pcp input machineInputLength
      bound compilerBits compilerFuel)

end NearCubicWires.TotalStructuralAtomEmitterProgram

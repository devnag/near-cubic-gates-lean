import Proof.MachineModel.StructuralAtomCalleeProgram
import Proof.MachineModel.TotalSelectiveCountCasesProgram

/-!
# The guarded structural formula program

The published structural atom callee hard-wires the original count-cases
compiler.  This module changes exactly that executable field.  The compiler
contract, the structural-formula stream, and the final atom projection are
parameterized by one `NPOracleProgram`; all semantic inputs and outputs remain
the published ones.
-/

namespace NearCubicWires.TotalStructuralAtomCalleeProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalSelectiveFixedCountProgram
open NearCubicWires.VerifiedLinker

open private structuralCompilerInputAdapterBits
  structuralCompilerInputAdapterProgram
  structuralCompilerRequestCode
  structuralCompilerSummaryInput
  structuralControllerContext
  structuralFormulaPipelineBitBudgets
  structuralPreludeBits
  structuralPreludeFuel
  structuralPreludeProgram
  structuralSummaryAdapterBits
  structuralSummaryAdapterInput
  structuralSummaryAdapterOutput
  structuralSummaryAdapterProgram
  structuralSummaryBits
  structuralSummaryFuel
  structuralSummaryProgram
  structuralSummaryTailProgram
  structuralWorkingValue_le
  run_structuralCompilerInputAdapterProgram
  run_structuralPreludeProgram
  run_structuralSummaryAdapterProgram
  run_structuralSummaryProgram_eq_response
  structuralSummaryAdapterOutput_eq_compilerSummary from
    Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The one-field compiler contract -/

/-- The exact pointwise compiler contract with executable ownership exposed. -/
def StructuralCompilerProgramRunsAt
    (compilerProgram : NPOracleProgram)
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (machineInputLength bound index compilerBits compilerFuel : ℕ) : Prop :=
  runNPOracleProgram compilerProgram compilerBits compilerFuel
      (initialNPOracleState machineInputLength <|
        structuralCompilerCoreInput (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) bound index) =
    some
      (selectiveWireCode
        (selectiveCompileTableBoundedOracleVerifier
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound
          (index - descriptionWidth (pcp.nativeWidth n) bound)))

theorem structuralCompilerProgramRunsAt_total
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound index : ℕ)
    (runner :
      SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
        (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
        (pcp.queryCount n) bound) :
    StructuralCompilerProgramRunsAt totalSelectiveCountCasesProgram pcp input
      machineInputLength bound index
      (selectiveCountCasesRunBits (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound runner index)
      (selectiveCountCasesRunFuel (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound runner index) := by
  exact run_totalSelectiveCountCasesProgram
    (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
    (pcp.queryCount n) bound runner machineInputLength index

/-! ## 2. The structural-formula stream with one program field -/

private def structuralCompilerTailProgramFor
    (compilerProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (preserveRightProgram compilerProgram)
    structuralSummaryTailProgram

/-- The published pointwise formula stream with only its compiler replaced. -/
def structuralFormulaProgramFor
    (compilerProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms structuralPreludeProgram <|
    linkPrograms structuralCompilerInputAdapterProgram
      (structuralCompilerTailProgramFor compilerProgram)

/-- Fuel for the program-parametric pointwise formula stream. -/
def structuralFormulaPipelineFuelFor
    (compilerProgram : NPOracleProgram) (outputs : List ℕ)
    (width count bound index compilerFuel : ℕ) : ℕ :=
  let inputArity := descriptionWidth width bound
  let compiled :=
    selectiveCompileTableBoundedOracleVerifier
      outputs width count bound (index - inputArity)
  let summaryFuel :=
    structuralSummaryFuel inputArity index
      (selectiveSelectedCode compiled.state.selected)
  let summaryTailFuel :=
    linkFuel structuralSummaryProgram 17 summaryFuel
  let compilerTailFuel :=
    linkFuel structuralSummaryTailProgram
      (preserveRightFuel compilerFuel) summaryTailFuel
  let compilerPipelineFuel :=
    linkFuel (structuralCompilerTailProgramFor compilerProgram)
      33 compilerTailFuel
  linkFuel
    (linkPrograms structuralCompilerInputAdapterProgram
      (structuralCompilerTailProgramFor compilerProgram))
    (structuralPreludeFuel outputs bound) compilerPipelineFuel

set_option maxHeartbeats 2000000 in
-- Linking the concrete compiler forces elaboration of the complete stream.
theorem run_structuralFormulaProgramFor
    (compilerProgram : NPOracleProgram)
    (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits compilerFuel : ℕ)
    (hcompiler :
      let inputArity := descriptionWidth width bound
      let compiled :=
        selectiveCompileTableBoundedOracleVerifier
          outputs width count bound (index - inputArity)
      runNPOracleProgram compilerProgram compilerBits compilerFuel
          (initialNPOracleState machineInputLength <|
            structuralCompilerCoreInput outputs width count bound index) =
        some (selectiveWireCode compiled)) :
    runNPOracleProgram (structuralFormulaProgramFor compilerProgram)
        (structuralFormulaPipelineBits machineInputLength outputs
          width count bound index compilerBits)
        (structuralFormulaPipelineFuelFor compilerProgram
          outputs width count bound index compilerFuel)
        (initialNPOracleState machineInputLength <|
          structuralFormulaRequestCode outputs width count bound index) =
      some (structuralFormulaResponseCode outputs width count bound index) := by
  let inputArity := descriptionWidth width bound
  let compiled :=
    selectiveCompileTableBoundedOracleVerifier
      outputs width count bound (index - inputArity)
  let compilerInput :=
    structuralCompilerCoreInput outputs width count bound index
  let compilerResult := selectiveWireCode compiled
  let summaryContext := Nat.pair inputArity index
  let preservedOutput := Nat.pair compilerResult summaryContext
  let summaryInput :=
    structuralCompilerSummaryInput outputs width count bound index
  let preludeBits :=
    structuralPreludeBits
      machineInputLength outputs width count bound index
  let adapterBits :=
    structuralCompilerInputAdapterBits outputs width count bound index
  let preservedBits :=
    preserveRightBits compilerBits compilerInput summaryContext compilerResult
  let summaryAdapterBits :=
    structuralSummaryAdapterBits compilerResult inputArity index
  let summaryBits :=
    structuralSummaryBits inputArity index compiled.state.next
      (selectiveSelectedCode compiled.state.selected) compiled.output
  let maximumBits :=
    structuralFormulaPipelineBits machineInputLength outputs
      width count bound index compilerBits
  let summaryFuel :=
    structuralSummaryFuel inputArity index
      (selectiveSelectedCode compiled.state.selected)
  let summaryTailFuel :=
    linkFuel structuralSummaryProgram 17 summaryFuel
  let compilerTailFuel :=
    linkFuel structuralSummaryTailProgram
      (preserveRightFuel compilerFuel) summaryTailFuel
  let compilerPipelineFuel :=
    linkFuel (structuralCompilerTailProgramFor compilerProgram)
      33 compilerTailFuel
  have hbudget : ∀ {value : ℕ},
      value ∈ structuralFormulaPipelineBitBudgets
          machineInputLength outputs width count bound index compilerBits →
        value ≤ maximumBits := by
    intro value hvalue
    exact structuralWorkingValue_le hvalue
  have hlengthBits :
      natBitLength machineInputLength ≤ maximumBits :=
    hbudget (by simp [structuralFormulaPipelineBitBudgets])
  have hpreludeBits : preludeBits ≤ maximumBits :=
    hbudget (by
      simp [structuralFormulaPipelineBitBudgets, preludeBits])
  have hadapterBits : adapterBits ≤ maximumBits :=
    hbudget (by
      simp [structuralFormulaPipelineBitBudgets, adapterBits])
  have hpreservedBits : preservedBits ≤ maximumBits :=
    hbudget (by
      simp [structuralFormulaPipelineBitBudgets, preservedBits,
        compilerInput, compilerResult, summaryContext, inputArity, compiled])
  have hsummaryAdapterBits : summaryAdapterBits ≤ maximumBits :=
    hbudget (by
      simp [structuralFormulaPipelineBitBudgets, summaryAdapterBits,
        compilerResult, inputArity, compiled])
  have hsummaryBits : summaryBits ≤ maximumBits :=
    hbudget (by
      simp [structuralFormulaPipelineBitBudgets, summaryBits,
        inputArity, compiled])
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength machineInputLength).trans hlengthBits
  have hprelude :
      runNPOracleProgram structuralPreludeProgram maximumBits
          (structuralPreludeFuel outputs bound)
          (initialNPOracleState machineInputLength <|
            structuralFormulaRequestCode outputs width count bound index) =
        some (structuralControllerContext outputs width count bound index) :=
    run_bits_mono
      (run_structuralPreludeProgram machineInputLength outputs
        width count bound index)
      hpreludeBits
  have hadapter :
      runNPOracleProgram structuralCompilerInputAdapterProgram maximumBits 33
          (initialNPOracleState machineInputLength <|
            structuralControllerContext outputs width count bound index) =
        some (structuralCompilerRequestCode
          outputs width count bound index) :=
    run_bits_mono
      (run_structuralCompilerInputAdapterProgram
        machineInputLength outputs width count bound index)
      hadapterBits
  have hcompilerOwn :
      runNPOracleProgram compilerProgram compilerBits compilerFuel
          (initialNPOracleState machineInputLength compilerInput) =
        some compilerResult := by
    simpa only [compilerInput, compilerResult, compiled, inputArity] using
      hcompiler
  have hpreservedOwn :
      runNPOracleProgram (preserveRightProgram compilerProgram)
          preservedBits (preserveRightFuel compilerFuel)
          (initialNPOracleState machineInputLength <|
            Nat.pair compilerInput summaryContext) =
        some preservedOutput := by
    simpa only [preservedBits, preservedOutput] using
      run_preserveRightProgram compilerProgram machineInputLength compilerBits
        compilerFuel compilerInput summaryContext compilerResult hcompilerOwn
  have hpreserved :
      runNPOracleProgram (preserveRightProgram compilerProgram)
          maximumBits (preserveRightFuel compilerFuel)
          (initialNPOracleState machineInputLength <|
            Nat.pair compilerInput summaryContext) =
        some preservedOutput :=
    run_bits_mono hpreservedOwn hpreservedBits
  have hsummaryAdapterOwn :
      runNPOracleProgram structuralSummaryAdapterProgram summaryAdapterBits 17
          (initialNPOracleState machineInputLength preservedOutput) =
        some
          (structuralSummaryAdapterOutput compilerResult inputArity index) := by
    simpa only [summaryAdapterBits, preservedOutput, summaryContext,
      structuralSummaryAdapterInput] using
      run_structuralSummaryAdapterProgram machineInputLength
        compilerResult inputArity index
  have hsummaryAdapter :
      runNPOracleProgram structuralSummaryAdapterProgram maximumBits 17
          (initialNPOracleState machineInputLength preservedOutput) =
        some summaryInput := by
    have hwiden :=
      run_bits_mono hsummaryAdapterOwn hsummaryAdapterBits
    have houtput :=
      structuralSummaryAdapterOutput_eq_compilerSummary
        outputs width count bound index
    simpa only [summaryInput, compilerResult, inputArity, compiled] using
      houtput ▸ hwiden
  have hsummaryOwn :
      runNPOracleProgram structuralSummaryProgram summaryBits summaryFuel
          (initialNPOracleState machineInputLength summaryInput) =
        some
          (structuralFormulaResponseCode
            outputs width count bound index) := by
    simpa only [summaryBits, summaryFuel, summaryInput, compiled, inputArity]
      using run_structuralSummaryProgram_eq_response
        machineInputLength outputs width count bound index
  have hsummary :
      runNPOracleProgram structuralSummaryProgram maximumBits summaryFuel
          (initialNPOracleState machineInputLength summaryInput) =
        some
          (structuralFormulaResponseCode
            outputs width count bound index) :=
    run_bits_mono hsummaryOwn hsummaryBits
  have hsummaryTail :
      runNPOracleProgram structuralSummaryTailProgram maximumBits
          summaryTailFuel
          (initialNPOracleState machineInputLength preservedOutput) =
        some
          (structuralFormulaResponseCode
            outputs width count bound index) := by
    exact run_linkPrograms hpositive hlengthBits hsummaryAdapter hsummary
  have hcompilerTail :
      runNPOracleProgram
          (structuralCompilerTailProgramFor compilerProgram)
          maximumBits compilerTailFuel
          (initialNPOracleState machineInputLength <|
            Nat.pair compilerInput summaryContext) =
        some
          (structuralFormulaResponseCode
            outputs width count bound index) := by
    exact run_linkPrograms hpositive hlengthBits hpreserved hsummaryTail
  have hrequest :
      structuralCompilerRequestCode outputs width count bound index =
        Nat.pair compilerInput summaryContext := by
    rfl
  change
    runNPOracleProgram
        (linkPrograms structuralPreludeProgram
          (linkPrograms structuralCompilerInputAdapterProgram
            (structuralCompilerTailProgramFor compilerProgram)))
        maximumBits
        (structuralFormulaPipelineFuelFor compilerProgram
          outputs width count bound index compilerFuel)
        (initialNPOracleState machineInputLength <|
          structuralFormulaRequestCode outputs width count bound index) =
      some (structuralFormulaResponseCode outputs width count bound index)
  rw [show structuralFormulaPipelineFuelFor compilerProgram
      outputs width count bound index compilerFuel =
    linkFuel
      (linkPrograms structuralCompilerInputAdapterProgram
        (structuralCompilerTailProgramFor compilerProgram))
      (structuralPreludeFuel outputs bound)
      (linkFuel (structuralCompilerTailProgramFor compilerProgram)
        33 compilerTailFuel) by
    rfl]
  exact run_linkPrograms hpositive hlengthBits hprelude <|
    run_linkPrograms hpositive hlengthBits hadapter <| by
      simpa only [hrequest] using hcompilerTail

end NearCubicWires.TotalStructuralAtomCalleeProgram

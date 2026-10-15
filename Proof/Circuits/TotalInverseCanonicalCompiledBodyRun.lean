import Proof.Circuits.TotalInverseCanonicalCompilerRuns
import Proof.Circuits.TotalSelectorDrivenBranchSensitiveRun

/-! # Total compiled inverse body with its canonical compiler installed -/

namespace NearCubicWires.TotalInverseCanonicalCompiledBodyRun

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseSelectorCompiledBody
open NearCubicWires.TotalSelectorDrivenBranchSensitiveRun
open NearCubicWires.UniformTargetTotalRun

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1600000 in
-- The exact guarded stream and canonical compiler resources normalize together.
/-- The exact selector-compiled inverse body is total with the canonical
guarded compiler installed.  No compiler-run proposition is supplied by the
caller. -/
theorem totalBooleanRuns_totalInverseSelectorCompiledBody_canonicalCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (rangeBits : ℕ → ℕ)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (inverseAtomContext contracts clockDepth machine advantageExponent
                pcp target)
              0
              (inverseAtomCount contracts clockDepth machine advantageExponent
                pcp target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)
              (inverseScheduleBound contracts clockDepth advantageExponent
                target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          index
          (totalInverseCanonicalCompilerBits contracts clockDepth machine
            advantageExponent pcp target index) ≤
        rangeBits target) :
    TotalBooleanRuns
      (totalInverseSelectorCompiledBody contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorCompiledBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits
        (totalInverseCanonicalCompilerBits contracts clockDepth machine
          advantageExponent pcp))
      (totalInverseSelectorCompiledBodyFuel contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFuel contracts clockDepth machine
          advantageExponent pcp))
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent) := by
  exact totalBooleanRuns_totalInverseSelectorCompiledBody contracts clockDepth
    machine advantageExponent pcp hpresentation rangeBits
    (totalInverseCanonicalCompilerBits contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseCanonicalCompilerFuel contracts clockDepth machine
      advantageExponent pcp)
    hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits
    (totalInverseCanonicalCompilerRuns contracts clockDepth machine
      advantageExponent pcp)

end NearCubicWires.TotalInverseCanonicalCompiledBodyRun

import Proof.Circuits.TotalSelectorDrivenAtomStreamRuns
import Proof.Circuits.TotalSelectorDrivenOccurrenceClosure

/-! # Concrete total selector occurrence chain -/

namespace NearCubicWires.TotalSelectorDrivenConcreteOccurrenceRuns

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseSelectorOccurrenceEncodingClosure
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseSelectorAtomStreamClosure
open NearCubicWires.TotalSelectorDrivenAtomStreamRuns
open NearCubicWires.TotalSelectorDrivenOccurrenceClosure
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts

set_option maxHeartbeats 1600000 in
-- The specialization expands the full guarded stream and encoding tower.
/-- The selector compiler supplies the exact total per-block occurrence program
used by the concrete compiled direct body. -/
theorem totalInverseScheduledOccurrenceRuns_ofSelectorCompiler
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
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
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
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel) :
    TotalInverseScheduledOccurrenceRuns contracts clockDepth machine
      advantageExponent
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent
        (inverseSelectorClosedEncodingProgram contracts clockDepth machine
          advantageExponent
          (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
            advantageExponent pcp)))
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent
        (inverseSelectorClosedEncodingBits contracts clockDepth machine
          advantageExponent
          (totalInverseSelectorAtomStreamBits contracts clockDepth machine
            advantageExponent pcp rangeBits compilerBits)))
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent
        (inverseSelectorClosedEncodingProgram contracts clockDepth machine
          advantageExponent
          (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
            advantageExponent pcp))
        (inverseSelectorClosedEncodingFuel contracts clockDepth machine
          advantageExponent
          (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
            advantageExponent pcp)
          (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
            advantageExponent pcp compilerFuel))) := by
  have hstream :=
    totalInverseDescriptionAtomStreamTotalRuns_ofSelectorCompiler contracts
      clockDepth machine advantageExponent pcp hpresentation rangeBits
      compilerBits compilerFuel hpositive hlengthBits hrangeBits hlistBits
      hcallBits hcalleeBits hcompiler
  have hencoding := totalInverseScheduledOccurrenceEncoding_ofAtomStream
    contracts clockDepth machine advantageExponent
    (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseSelectorAtomStreamBits contracts clockDepth machine
      advantageExponent pcp rangeBits compilerBits)
    (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    hstream
  exact totalInverseScheduledOccurrenceRuns_ofSelectorEncoding contracts
    clockDepth machine advantageExponent
    (inverseSelectorClosedEncodingProgram contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp))
    (inverseSelectorClosedEncodingBits contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits))
    (inverseSelectorClosedEncodingFuel contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel))
    hencoding

end NearCubicWires.TotalSelectorDrivenConcreteOccurrenceRuns

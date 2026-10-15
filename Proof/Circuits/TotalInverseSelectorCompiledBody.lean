import Proof.Circuits.TotalInverseSelectorAtomStreamClosure
import Proof.Circuits.TotalInverseSelectorDirectBodyClosure

/-!
# The guarded selector-compiled direct body

This module installs the concrete guarded description atom stream into the
guarded direct body and exports the selector-compiler convenience theorem.
-/

namespace NearCubicWires.TotalInverseSelectorCompiledBody

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseSelectorDirectBodyClosure
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalInverseSelectorAtomStreamClosure
open NearCubicWires.TotalInverseSelectorDirectBodyClosure
open NearCubicWires.TotalBankEmittedAtomLoop

noncomputable def totalInverseSelectorCompiledBody
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  totalInverseSelectorDirectBody contracts clockDepth machine advantageExponent
    pcp
    (inverseSelectorClosedEncodingProgram contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp))

noncomputable def totalInverseSelectorCompiledBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (rangeBits : ℕ → ℕ) (compilerBits : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  totalInverseSelectorDirectBodyBits contracts clockDepth machine
    advantageExponent pcp rangeBits compilerBits
    (inverseSelectorClosedEncodingBits contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits))

noncomputable def totalInverseSelectorCompiledBodyFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  totalInverseSelectorDirectBodyFuel contracts clockDepth machine
    advantageExponent pcp compilerFuel
    (inverseSelectorClosedEncodingProgram contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp))
    (inverseSelectorClosedEncodingFuel contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel))

set_option maxHeartbeats 1600000 in
-- The convenience theorem expands the guarded stream, encoding, and body ABIs.
theorem totalInverseSelectorDirectBodyRun_ofSelectorCompiler
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
    InverseSelectorDirectBodyRun contracts clockDepth machine advantageExponent
      (totalInverseSelectorCompiledBody contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorCompiledBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits)
      (totalInverseSelectorCompiledBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) := by
  have hstream :=
    totalInverseDescriptionAtomStreamRuns_ofSelectorCompiler contracts
      clockDepth machine advantageExponent pcp hpresentation rangeBits
      compilerBits compilerFuel hpositive hlengthBits hrangeBits hlistBits
      hcallBits hcalleeBits hcompiler
  exact totalInverseSelectorDirectBodyRun_ofAtomStream contracts clockDepth
    machine advantageExponent pcp hpresentation rangeBits compilerBits
    compilerFuel hpositive hlengthBits hrangeBits hlistBits hcallBits
    hcalleeBits hcompiler
    (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseSelectorAtomStreamBits contracts clockDepth machine
      advantageExponent pcp rangeBits compilerBits)
    (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    hstream

end NearCubicWires.TotalInverseSelectorCompiledBody

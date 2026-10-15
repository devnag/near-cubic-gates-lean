import Proof.Circuits.InverseSelectorDirectBodyClosure
import Proof.Circuits.TotalSelectorBodyAdapter
import Proof.Circuits.TotalSelectorDrivenEmitterRuns

/-!
# The guarded inverse selector direct body

The two direct register chains and occurrence encoding are frozen. This module
replaces only the selector-frame adapter and bank emitter, exposes their exact
program/bit/fuel ownership, and retains the existing
`InverseSelectorDirectBodyRun` result ABI.
-/

namespace NearCubicWires.TotalInverseSelectorDirectBodyClosure

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseSelectorDirectBodyClosure
open NearCubicWires.InverseSelectorOccurrenceEncodingClosure
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.InverseTotalScheduledRowStageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyClosure
open NearCubicWires.SelectorDrivenBodyDispatch
open NearCubicWires.SelectorDrivenEmitterRuns
open NearCubicWires.SelectorDrivenRegisterCaseOneChain
open NearCubicWires.SelectorDrivenRegisterCaseTwoChain
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TotalSelectorDrivenEmitterRuns
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Exact guarded program and resources -/

noncomputable def totalInverseSelectorDirectBody
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (encodingProgram : NPOracleProgram) : NPOracleProgram :=
  bankDispatchedBodyProgram
    (emittedBranchSelectorProgram
      (totalInverseBankEmitterProgram
        (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
          advantageExponent pcp)))
    (inverseSelectorCaseOneProgram contracts clockDepth machine
      (inverseTotalScheduledRowProgram contracts clockDepth))
    (inverseSelectorCaseTwoProgram contracts
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram))

noncomputable def totalInverseSelectorDirectBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (rangeBits : ℕ → ℕ) (compilerBits : ℕ → ℕ → ℕ)
    (encodingBits : ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  bankDispatchedBodyBitsAtFrame
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
    (inverseBankSelectorBitsAtFrame contracts clockDepth machine
      advantageExponent
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
      (totalInverseSelectorBankEmitterBits contracts clockDepth machine
        advantageExponent pcp
        (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
          advantageExponent pcp compilerBits)
        rangeBits))
    (inverseSelectorDirectChainBits contracts clockDepth machine
      advantageExponent
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits))

noncomputable def totalInverseSelectorDirectBodyFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (encodingProgram : NPOracleProgram)
    (encodingFuel : ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  bankDispatchedBodyFuel
    (inverseSelectorCaseOneProgram contracts clockDepth machine
      (inverseTotalScheduledRowProgram contracts clockDepth))
    (inverseSelectorCaseTwoProgram contracts
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram))
    (inverseBankSelectorFuel contracts clockDepth machine advantageExponent
      (totalInverseBankEmitterFuel contracts clockDepth machine
        advantageExponent pcp
        (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
          advantageExponent pcp compilerFuel)
        compilerFuel))
    (inverseSelectorDirectChainFuel contracts clockDepth machine
      advantageExponent (inverseTotalScheduledRowProgram contracts clockDepth)
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram)
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel))

/-! ## 2. Guarded direct body from an occurrence encoding -/

set_option maxHeartbeats 1600000 in
-- The direct body expands both dependent branch programs and resource envelopes.
theorem totalInverseSelectorDirectBodyRun_ofEncoding
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
        pcp compilerBits compilerFuel)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencoding :
      InverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    InverseSelectorDirectBodyRun contracts clockDepth machine advantageExponent
      (totalInverseSelectorDirectBody contracts clockDepth machine
        advantageExponent pcp encodingProgram)
      (totalInverseSelectorDirectBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits encodingBits)
      (totalInverseSelectorDirectBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel encodingProgram encodingFuel) := by
  unfold InverseSelectorDirectBodyRun
  have hrow := inverseTotalScheduledRowRuns contracts clockDepth machine
    advantageExponent
  have hoccurrence :=
    inverseScheduledOccurrenceRuns_ofSelectorEncoding contracts clockDepth
      machine advantageExponent encodingProgram encodingBits encodingFuel
      hencoding
  exact inverse_bodyRun_of_emitterRuns_atFrame contracts clockDepth machine
    advantageExponent
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
    (totalInverseBankEmitterProgram
      (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp))
    (inverseSelectorCaseOneProgram contracts clockDepth machine
      (inverseTotalScheduledRowProgram contracts clockDepth))
    (inverseSelectorCaseTwoProgram contracts
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram))
    (totalInverseSelectorBankEmitterBits contracts clockDepth machine
      advantageExponent pcp
      (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits)
      rangeBits)
    (totalInverseBankEmitterFuel contracts clockDepth machine advantageExponent
      pcp
      (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel)
      compilerFuel)
    (inverseSelectorDirectChainBits contracts clockDepth machine
      advantageExponent
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits))
    (inverseSelectorDirectChainFuel contracts clockDepth machine
      advantageExponent (inverseTotalScheduledRowProgram contracts clockDepth)
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram)
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel))
    (totalInverseSelectorEmitterRuns_ofCompiler contracts clockDepth machine
      advantageExponent pcp
      (inverseScheduleAtoms_of_presentation contracts clockDepth machine
        advantageExponent pcp hpresentation)
      (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits)
      (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel)
      rangeBits compilerBits compilerFuel
      (totalInverseSelectorBodyAdapterRuns contracts clockDepth machine
        advantageExponent pcp hpresentation compilerBits compilerFuel hcompiler)
      hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits hcompiler)
    (inverse_selectorCaseOneChain_ofRow contracts clockDepth machine
      advantageExponent (inverseTotalScheduledRowProgram contracts clockDepth)
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram)
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel)
      hrow)
    (inverse_selectorCaseTwoChain_ofOccurrence contracts clockDepth machine
      advantageExponent (inverseTotalScheduledRowProgram contracts clockDepth)
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram)
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel)
      hoccurrence)

/-! ## 3. Atom-stream specialization -/

set_option maxHeartbeats 1600000 in
-- The atom-stream specialization retains the full compiler and range ledger.
theorem totalInverseSelectorDirectBodyRun_ofAtomStream
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
        pcp compilerBits compilerFuel)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      InverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    InverseSelectorDirectBodyRun contracts clockDepth machine advantageExponent
      (totalInverseSelectorDirectBody contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorClosedEncodingProgram contracts clockDepth machine
          advantageExponent stream))
      (totalInverseSelectorDirectBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits
        (inverseSelectorClosedEncodingBits contracts clockDepth machine
          advantageExponent streamBits))
      (totalInverseSelectorDirectBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel
        (inverseSelectorClosedEncodingProgram contracts clockDepth machine
          advantageExponent stream)
        (inverseSelectorClosedEncodingFuel contracts clockDepth machine
          advantageExponent stream streamFuel)) :=
  totalInverseSelectorDirectBodyRun_ofEncoding contracts clockDepth machine
    advantageExponent pcp hpresentation rangeBits compilerBits compilerFuel
    hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits hcompiler
    (inverseSelectorClosedEncodingProgram contracts clockDepth machine
      advantageExponent stream)
    (inverseSelectorClosedEncodingBits contracts clockDepth machine
      advantageExponent streamBits)
    (inverseSelectorClosedEncodingFuel contracts clockDepth machine
      advantageExponent stream streamFuel)
    (inverseScheduledOccurrenceEncoding_ofAtomStream contracts clockDepth
      machine advantageExponent stream streamBits streamFuel hstream)

end NearCubicWires.TotalInverseSelectorDirectBodyClosure

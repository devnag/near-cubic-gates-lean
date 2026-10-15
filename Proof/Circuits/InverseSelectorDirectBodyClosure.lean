import Proof.Circuits.InverseSelectorOccurrenceEncodingClosure
import Proof.Circuits.InverseTotalScheduledRowStageClosure
import Proof.CaseAnalysis.SelectorDrivenRegisterCaseTwoChain

/-!
# The inverse selector body with both direct register chains installed

Case One uses the total guarded row program.  Case Two uses the selector-driven
occurrence runner assembled from one substituted-circuit encoding stream.  The
body therefore exposes only the emitter/compiler and range-width obligations;
neither a schedule diagonal nor query-count positivity remains.
-/

namespace NearCubicWires.InverseSelectorDirectBodyClosure

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseSelectorOccurrenceEncodingClosure
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.InverseTotalScheduledRowStageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
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
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

noncomputable def inverseSelectorDirectBody
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
      (inverseBankEmitterProgram
        (inverseSelectorBodyAdapterProgram contracts clockDepth machine
          advantageExponent pcp)))
    (inverseSelectorCaseOneProgram contracts clockDepth machine
      (inverseTotalScheduledRowProgram contracts clockDepth))
    (inverseSelectorCaseTwoProgram contracts
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram))

noncomputable def inverseSelectorDirectBodyBits
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
      (inverseSelectorBankEmitterBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorBodyAdapterBits contracts clockDepth machine
          advantageExponent pcp compilerBits)
        rangeBits))
    (inverseSelectorDirectChainBits contracts clockDepth machine
      advantageExponent
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits))

noncomputable def inverseSelectorDirectBodyFuel
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
      (inverseBankEmitterFuel contracts clockDepth machine advantageExponent pcp
        (inverseSelectorBodyAdapterFuel contracts clockDepth machine
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

def InverseSelectorDirectBodyRun
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ target
    (hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (hrejects :
      ¬machine.toSemantic.accepts
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (haccepts :
      ∀ branchTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target),
        InverseCaseTwoAcceptance contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent)
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target)
          branchTwo machine),
    ∀ input : BitInput target,
      runNPOracleProgram body (bodyBits ⟨target, input⟩)
          (bodyFuel ⟨target, input⟩)
          (initialNPOracleState target
            (inverseSelectorAdapterFrame contracts clockDepth
              advantageExponent ⟨target, input⟩)) =
        some
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts input).toNat

set_option maxHeartbeats 1600000 in
-- The direct body type expands both dependent branch programs and envelopes.
theorem inverseSelectorDirectBodyRun_ofEncoding
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
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencoding :
      InverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    InverseSelectorDirectBodyRun contracts clockDepth machine advantageExponent
      (inverseSelectorDirectBody contracts clockDepth machine advantageExponent
        pcp encodingProgram)
      (inverseSelectorDirectBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits encodingBits)
      (inverseSelectorDirectBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel encodingProgram encodingFuel) := by
  unfold InverseSelectorDirectBodyRun
  have hrow := inverseTotalScheduledRowRuns contracts clockDepth machine
    advantageExponent
  have hoccurrence :=
    inverseScheduledOccurrenceRuns_ofSelectorEncoding contracts clockDepth
      machine advantageExponent encodingProgram encodingBits encodingFuel
      hencoding
  exact inverse_bodyRun_ofSelectorBank contracts clockDepth machine
    advantageExponent pcp hpresentation
    (inverseSelectorCaseOneProgram contracts clockDepth machine
      (inverseTotalScheduledRowProgram contracts clockDepth))
    (inverseSelectorCaseTwoProgram contracts
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram))
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
    rangeBits compilerBits compilerFuel hpositive hlengthBits hrangeBits
    hlistBits hcallBits hcalleeBits hcompiler
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

set_option maxHeartbeats 1600000 in
-- The atom-stream specialization retains the full compiler and range ledger.
theorem inverseSelectorDirectBodyRun_ofAtomStream
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
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      InverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    InverseSelectorDirectBodyRun contracts clockDepth machine advantageExponent
      (inverseSelectorDirectBody contracts clockDepth machine advantageExponent
        pcp
        (inverseSelectorClosedEncodingProgram contracts clockDepth machine
          advantageExponent stream))
      (inverseSelectorDirectBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits
        (inverseSelectorClosedEncodingBits contracts clockDepth machine
          advantageExponent streamBits))
      (inverseSelectorDirectBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel
        (inverseSelectorClosedEncodingProgram contracts clockDepth machine
          advantageExponent stream)
        (inverseSelectorClosedEncodingFuel contracts clockDepth machine
          advantageExponent stream streamFuel)) :=
  inverseSelectorDirectBodyRun_ofEncoding contracts clockDepth machine
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

end NearCubicWires.InverseSelectorDirectBodyClosure

import Proof.CaseAnalysis.TotalSelectorDrivenCaseOneRun
import Proof.CaseAnalysis.TotalSelectorDrivenCaseTwoRun
import Proof.Circuits.TotalSelectorDrivenConcreteOccurrenceRuns
import Proof.Circuits.TotalSelectorDrivenEmitterTotalRuns
import Proof.Circuits.TotalSelectorDrivenHierarchyAcceptance
import Proof.Circuits.TotalSelectorDrivenSelectorRun
import Proof.Circuits.TotalInverseSelectorCompiledBody

/-! # Branch-sensitive all-request selector body run -/

namespace NearCubicWires.TotalSelectorDrivenBranchSensitiveRun

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBranchSelectorProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
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
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyDispatch
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseSelectorAtomStreamClosure
open NearCubicWires.TotalInverseSelectorCompiledBody
open NearCubicWires.TotalInverseSelectorDirectBodyClosure
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenAtomStreamRuns
open NearCubicWires.TotalSelectorDrivenBodyAdapterRuns
open NearCubicWires.TotalSelectorDrivenCaseOneRun
open NearCubicWires.TotalSelectorDrivenCaseTwoRun
open NearCubicWires.TotalSelectorDrivenConcreteOccurrenceRuns
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TotalSelectorDrivenEmitterTotalRuns
open NearCubicWires.TotalSelectorDrivenEmitterTotalContract
open NearCubicWires.TotalSelectorDrivenHierarchyAcceptance
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts
open NearCubicWires.TotalSelectorDrivenSelectorResources
open NearCubicWires.UniformTargetTotalRun
open NearCubicWires.VerifiedLinker

open private branchTargetBitBits_mono_output from
  Proof.MachineModel.BankDispatchedTargetBody

/-- Exact dependent adapter from a canonical inverse-schedule oracle to the
hierarchy acceptance fact consumed by the branch constructor. -/
private theorem hierarchy_accepts_inverseSchedule_of_canonicalOracle
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (oracle : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)) :
    (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
      (sourceLength
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent target))
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target) := by
  exact hierarchy_accepts_of_canonicalAcceptingOracle
    (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
      advantageExponent target)
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)
    oracle

set_option maxRecDepth 2000 in
-- The proof normalizes both exact selector tags and the two dependent chains.
set_option maxHeartbeats 1600000 in
-- The selector SAT tag is eliminated before the corresponding resource branch.
/-- A total emitter and a live-branch total occurrence callee make the direct
selector body total on every request.  Case Two is requested only after the
SAT tag supplies hierarchy acceptance and the canonical branch witness. -/
theorem totalBooleanRuns_bankDispatchedBodyProgram_branchSensitive
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (emitter : NPOracleProgram)
    (emitterBits emitterFuel : LanguageEvaluationRequest → ℕ)
    (hemitter :
      TotalInverseSelectorEmitterRuns contracts clockDepth machine
        advantageExponent emitter emitterBits emitterFuel)
    (occurrence : NPOracleProgram)
    (occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (hoccurrence :
      TotalInverseScheduledOccurrenceRuns contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel) :
    TotalBooleanRuns
      (bankDispatchedBodyProgram (emittedBranchSelectorProgram emitter)
        (inverseSelectorCaseOneProgram contracts clockDepth machine
          (inverseTotalScheduledRowProgram contracts clockDepth))
        (inverseSelectorCaseTwoProgram contracts occurrence))
      (bankDispatchedBodyBitsAtFrame
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
        (inverseBankSelectorBitsAtFrame contracts clockDepth machine
          advantageExponent
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
          emitterBits)
        (inverseSelectorDirectChainBits contracts clockDepth machine
          advantageExponent
          (inverseTotalScheduledRowBits contracts clockDepth machine
            advantageExponent)
          occurrenceBits))
      (bankDispatchedBodyFuel
        (inverseSelectorCaseOneProgram contracts clockDepth machine
          (inverseTotalScheduledRowProgram contracts clockDepth))
        (inverseSelectorCaseTwoProgram contracts occurrence)
        (inverseBankSelectorFuel contracts clockDepth machine
          advantageExponent emitterFuel)
        (inverseSelectorDirectChainFuel contracts clockDepth machine
          advantageExponent
          (inverseTotalScheduledRowProgram contracts clockDepth) occurrence
          (inverseTotalScheduledRowFuel contracts clockDepth machine
            advantageExponent)
          occurrenceFuel))
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent) := by
  intro request
  let frame :=
    inverseSelectorAdapterFrame contracts clockDepth advantageExponent request
  let selectorBits :=
    inverseBankSelectorBitsAtFrame contracts clockDepth machine
      advantageExponent
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
      emitterBits request
  let selectorFuel :=
    inverseBankSelectorFuel contracts clockDepth machine advantageExponent
      emitterFuel request
  let chainBits :=
    inverseSelectorDirectChainBits contracts clockDepth machine
      advantageExponent
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      occurrenceBits request
  let chainFuel :=
    inverseSelectorDirectChainFuel contracts clockDepth machine
      advantageExponent
      (inverseTotalScheduledRowProgram contracts clockDepth) occurrence
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent)
      occurrenceFuel request
  let query :=
    boundedOracleRecoveryCode
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        request.length)
      (inverseScheduleBound contracts clockDepth advantageExponent
        request.length)
  have hemits := by
    simpa only [inverseSelectorAtoms_eq] using hemitter request
  have hfirstTotal :=
    totalBooleanRuns_inverseSelectorCaseOneProgram contracts clockDepth machine
      advantageExponent occurrence occurrenceBits occurrenceFuel request
  rcases hfirstTotal with ⟨firstValue, hfirstValue, hfirst⟩
  by_cases htag : encodedSat query = false
  · refine ⟨firstValue, hfirstValue, ?_⟩
    have hselectorRaw := run_emittedBranchSelectorProgram
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        request.length)
      (inverseScheduleBound contracts clockDepth advantageExponent
        request.length)
      request.length frame frame (emitterBits request) (emitterFuel request)
      emitter hemits
    rw [htag] at hselectorRaw
    norm_num at hselectorRaw
    have hselector :
        runNPOracleProgram (emittedBranchSelectorProgram emitter) selectorBits
            selectorFuel (initialNPOracleState request.length frame) =
          some (Nat.pair 0 frame) := by
      simpa only [selectorBits, selectorFuel, frame,
        inverseBankSelectorBitsAtFrame_eq_schedule,
        inverseBankSelectorFuel_eq_schedule] using hselectorRaw
    have hrun := run_branchTargetBitProgram_caseOne
      (emittedBranchSelectorProgram emitter)
      (inverseSelectorCaseOneProgram contracts clockDepth machine
        (inverseTotalScheduledRowProgram contracts clockDepth))
      (inverseSelectorCaseTwoProgram contracts occurrence)
      request.length frame selectorBits selectorFuel chainBits chainFuel
      firstValue hselector hfirst
    have hwidth :
        branchTargetBitBits request.length 0 frame selectorBits chainBits
            firstValue ≤
          max
            (branchTargetBitBits request.length 0 frame selectorBits chainBits
              1)
            (branchTargetBitBits request.length 1 frame selectorBits chainBits
              1) :=
      (branchTargetBitBits_mono_output request.length 0 frame selectorBits
        chainBits firstValue hfirstValue).trans
          (Nat.le_max_left _ _)
    simpa only [bankDispatchedBodyProgram, bankDispatchedBodyBitsAtFrame,
      bankDispatchedBodyFuel, frame, selectorBits, selectorFuel, chainBits,
      chainFuel] using run_bits_mono hrun hwidth
  · have htrue : encodedSat query = true := Bool.eq_true_of_not_eq_false htag
    have hcanonical : Nonempty
        (CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            request.length)) := by
      apply (encodedSat_iff_nonempty_canonicalAcceptingOracle
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          request.length)).mp
      simpa only [query, inverseScheduleBound, inverseScheduleLength,
        scheduledWidth, paddedOuterPCP_nativeWidth] using htrue
    let oracle := Classical.choice hcanonical
    have hyes := hierarchy_accepts_inverseSchedule_of_canonicalOracle contracts
      clockDepth machine advantageExponent request.length oracle
    cases hbranch : inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent request.length hyes with
    | caseOne data =>
        exact (not_nonempty_canonicalAcceptingOracle_of_caseOneData data
          hcanonical).elim
    | caseTwo caseTwo =>
        let secondValue :=
          (((List.range
            (inverseChainTwoCopies contracts clockDepth advantageExponent
              request.length)).map
            (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
              caseTwo (encodeBitInput request.input))).foldl xor false).toNat
        have hsecondValue : secondValue ≤ 1 := by
          unfold secondValue
          cases ((List.range
              (inverseChainTwoCopies contracts clockDepth advantageExponent
                request.length)).map
              (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
                caseTwo (encodeBitInput request.input))).foldl xor false <;>
            simp
        refine ⟨secondValue, hsecondValue, ?_⟩
        have hselectorRaw := run_emittedBranchSelectorProgram
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            request.length)
          (inverseScheduleBound contracts clockDepth advantageExponent
            request.length)
          request.length frame frame (emitterBits request)
          (emitterFuel request) emitter hemits
        have htrueSchedule :
            encodedSat
                (boundedOracleRecoveryCode
                  (paddedOuterPCP
                    (publishedHierarchyOuterPCP contracts clockDepth))
                  (inverseScheduleInput contracts clockDepth machine
                    advantageExponent request.length)
                  (inverseScheduleBound contracts clockDepth advantageExponent
                    request.length)) = true := by
          simpa only [query] using htrue
        rw [htrueSchedule] at hselectorRaw
        norm_num at hselectorRaw
        have hselector :
            runNPOracleProgram (emittedBranchSelectorProgram emitter)
                selectorBits selectorFuel
                (initialNPOracleState request.length frame) =
              some (Nat.pair 1 frame) := by
          simpa only [selectorBits, selectorFuel, frame,
            inverseBankSelectorBitsAtFrame_eq_schedule,
            inverseBankSelectorFuel_eq_schedule] using hselectorRaw
        have hsecond :=
          run_inverseSelectorCaseTwoProgram_ofTotalOccurrence contracts
            clockDepth machine advantageExponent
            (inverseTotalScheduledRowProgram contracts clockDepth) occurrence
            (inverseTotalScheduledRowBits contracts clockDepth machine
              advantageExponent)
            (inverseTotalScheduledRowFuel contracts clockDepth machine
              advantageExponent)
            occurrenceBits occurrenceFuel hoccurrence request.length hyes
            caseTwo hbranch request.input
        have hrun := run_branchTargetBitProgram_caseTwo
          (emittedBranchSelectorProgram emitter)
          (inverseSelectorCaseOneProgram contracts clockDepth machine
            (inverseTotalScheduledRowProgram contracts clockDepth))
          (inverseSelectorCaseTwoProgram contracts occurrence)
          request.length frame 1 selectorBits selectorFuel chainBits chainFuel
          secondValue (by norm_num) hselector hsecond
        have hwidth :
            branchTargetBitBits request.length 1 frame selectorBits chainBits
                secondValue ≤
              max
                (branchTargetBitBits request.length 0 frame selectorBits
                  chainBits 1)
                (branchTargetBitBits request.length 1 frame selectorBits
                  chainBits 1) :=
          (branchTargetBitBits_mono_output request.length 1 frame selectorBits
            chainBits secondValue hsecondValue).trans
              (Nat.le_max_right _ _)
        simpa only [bankDispatchedBodyProgram, bankDispatchedBodyBitsAtFrame,
          bankDispatchedBodyFuel, frame, selectorBits, selectorFuel, chainBits,
          chainFuel, secondValue] using run_bits_mono hrun hwidth

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1600000 in
-- The specialization unfolds the exact guarded stream, encoding, and body ABI.
/-- The exact guarded selector-compiled inverse body is total on every request.
Its premises are only the published PCP presentation and the compiler/range
resource ledger; neither recovery branch is assumed unconditionally. -/
theorem totalBooleanRuns_totalInverseSelectorCompiledBody
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
    TotalBooleanRuns
      (totalInverseSelectorCompiledBody contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorCompiledBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits)
      (totalInverseSelectorCompiledBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent) := by
  have hadapter := totalInverseSelectorBodyAdapterTotalRuns contracts clockDepth
    machine advantageExponent pcp hpresentation compilerBits compilerFuel
    hcompiler
  have hemitter := totalInverseSelectorEmitterTotalRuns_ofCompiler contracts
    clockDepth machine advantageExponent pcp
    (inverseScheduleAtoms_of_presentation contracts clockDepth machine
      advantageExponent pcp hpresentation)
    (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
      advantageExponent pcp compilerBits)
    (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    rangeBits compilerBits compilerFuel hadapter hpositive hlengthBits
    hrangeBits hlistBits hcallBits hcalleeBits hcompiler
  have hoccurrence :=
    totalInverseScheduledOccurrenceRuns_ofSelectorCompiler contracts clockDepth
      machine advantageExponent pcp hpresentation rangeBits compilerBits
      compilerFuel hpositive hlengthBits hrangeBits hlistBits hcallBits
      hcalleeBits hcompiler
  have hbody :=
    totalBooleanRuns_bankDispatchedBodyProgram_branchSensitive contracts
      clockDepth machine advantageExponent
      (totalInverseBankEmitterProgram
        (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
          advantageExponent pcp))
      (totalInverseSelectorBankEmitterBits contracts clockDepth machine
        advantageExponent pcp
        (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
          advantageExponent pcp compilerBits)
        rangeBits)
      (totalInverseBankEmitterFuel contracts clockDepth machine
        advantageExponent pcp
        (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
          advantageExponent pcp compilerFuel)
        compilerFuel)
      hemitter
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
            advantageExponent pcp compilerFuel)))
      hoccurrence
  simpa only [totalInverseSelectorCompiledBody,
    totalInverseSelectorCompiledBodyBits, totalInverseSelectorCompiledBodyFuel,
    totalInverseSelectorDirectBody, totalInverseSelectorDirectBodyBits,
    totalInverseSelectorDirectBodyFuel] using hbody

end NearCubicWires.TotalSelectorDrivenBranchSensitiveRun

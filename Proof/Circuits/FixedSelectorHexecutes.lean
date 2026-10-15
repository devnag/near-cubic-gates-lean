import Proof.Circuits.SelectorDrivenLengthStage
import Proof.MachineModel.ExecutableTargetLanguagePackaging
import Proof.Circuits.UniformTargetTotalRun

/-!
# The fixed schedule's `hexecutes`, from the selector-driven bank

The fixed length stage already runs the schedule selector and constructs the
chain's own numeral frame with no diagonal premise.  This module links that
closed bank to an arbitrary register-driven body and packages the resulting
canonical run as the exact fixed-schedule `hexecutes` obligation.
-/

namespace NearCubicWires.FixedSelectorHexecutes

open NearCubicWires
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenLengthStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.UniformTargetTotalRun
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed selector-driven uniform target program -/

noncomputable def fixedSelectorUniformProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (publishedSourceDrivenBankProgram
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate)
      (fixedLengthProgram contracts clockDepth requestedRate))
    body

noncomputable def fixedSelectorChainIndex
    (contracts : PublishedContracts) (clockDepth requestedRate target : ℕ) : ℕ :=
  fixedSelectedSource contracts
    (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target

noncomputable def fixedSelectorUniformBits
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (bodyBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits request.length
    (publishedSourceDrivenBankBits
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate) request.length
      (fixedLengthBits contracts clockDepth requestedRate request)
      (fixedScheduleLength contracts clockDepth requestedRate request.length)
      request.code)
    (bodyBits request)

noncomputable def fixedSelectorUniformFuel
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram) (bodyFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel body
    (publishedSourceDrivenBankFuel
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate)
      (fixedLengthFuel contracts clockDepth requestedRate request)
      (fixedScheduleLength contracts clockDepth requestedRate request.length))
    (bodyFuel request)

noncomputable def fixedSelectorBodyFrame
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorDrivenBankFrame
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (fixedBankRate contracts requestedRate)
    (fixedSelectorChainIndex contracts clockDepth requestedRate request.length)
    request.code

/-- Whatever the body returns from the fixed selector frame is returned by the
whole linked stream from the public request. -/
theorem run_fixedSelectorUniformProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (target : ℕ) (input : BitInput target) (value : ℕ)
    (hbody :
      runNPOracleProgram body (bodyBits ⟨target, input⟩)
          (bodyFuel ⟨target, input⟩)
          (initialNPOracleState target
            (selectorDrivenBankFrame
              (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (fixedBankRate contracts requestedRate)
              (fixedSelectorChainIndex contracts clockDepth requestedRate
                target)
              (encodeBitInput input))) =
        some value) :
    runNPOracleProgram
        (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
        (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits
          ⟨target, input⟩)
        (fixedSelectorUniformFuel contracts clockDepth requestedRate body
          bodyFuel ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some value :=
  run_occurrenceStage
    (run_fixedSelectorBank_closed contracts clockDepth requestedRate target
      input)
    hbody

/-! ## 1b. Totality through the closed fixed selector bank -/

noncomputable def fixedSelectorTotalOutput
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  totalTargetOutput
    (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
    (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits)
    (fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel)

theorem totalBooleanRuns_fixedSelectorUniformProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedSelectorBodyFrame contracts clockDepth requestedRate)) :
    TotalBooleanRuns
      (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
      (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits)
      (fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel)
      LanguageEvaluationRequest.code := by
  intro request
  obtain ⟨value, hvalueLe, hvalue⟩ := hbody request
  exact ⟨value, hvalueLe,
    run_fixedSelectorUniformProgram contracts clockDepth requestedRate body
      bodyBits bodyFuel request.length request.input value hvalue⟩

theorem fixedSelector_hrun_of_totalBody
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedSelectorBodyFrame contracts clockDepth requestedRate)) :
    ∀ request : LanguageEvaluationRequest,
      runNPOracleProgram
          (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
          (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits
            request)
          (fixedSelectorUniformFuel contracts clockDepth requestedRate body
            bodyFuel request)
          (initialNPOracleState request.length request.code) =
        some
          (fixedSelectorTotalOutput contracts clockDepth requestedRate body
            bodyBits bodyFuel request) :=
  run_eq_totalTargetOutput _ _ _
    (totalBooleanRuns_fixedSelectorUniformProgram contracts clockDepth
      requestedRate body bodyBits bodyFuel hbody)

theorem fixedSelector_hboolean_of_totalBody
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (hbody :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedSelectorBodyFrame contracts clockDepth requestedRate)) :
    ∀ request : LanguageEvaluationRequest,
      fixedSelectorTotalOutput contracts clockDepth requestedRate body bodyBits
          bodyFuel request ≤ 1 :=
  totalTargetOutput_le_one _ _ _
    (totalBooleanRuns_fixedSelectorUniformProgram contracts clockDepth
      requestedRate body bodyBits bodyFuel hbody)

/-! ## 2. Canonical linked runs from a selector-frame body -/

theorem fixed_huniform_of_selectorBank
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (bodyRun : ∀ target
        (hlarge :
          fixedCaseOneTargetOnset contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
            target)
        (hyes :
          (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
            (sourceLength
              (fixedSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
                target))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
        (hrejects :
          ¬machine.toSemantic.accepts
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
        (haccepts :
          ∀ caseTwo : CanonicalAcceptingOracle
            (sizeBound := oracleSizeBound
              (fixedRequiredDegree contracts requestedRate))
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target),
            FixedCaseTwoAcceptance contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              (fixedSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
                target)
              caseTwo machine),
        ∀ input : BitInput target,
          runNPOracleProgram body (bodyBits ⟨target, input⟩)
              (bodyFuel ⟨target, input⟩)
              (initialNPOracleState target
                (selectorDrivenBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate)
                  (fixedSelectorChainIndex contracts clockDepth requestedRate
                    target)
                  (encodeBitInput input))) =
            some
              (fixedCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                requestedRate target hlarge hyes hrejects haccepts
                input).toNat) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
          target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (haccepts :
        ∀ caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)
            caseTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram
            (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
            (fixedSelectorUniformBits contracts clockDepth requestedRate
              bodyBits ⟨target, input⟩)
            (fixedSelectorUniformFuel contracts clockDepth requestedRate body
              bodyFuel ⟨target, input⟩)
            (initialNPOracleState target (encodeBitInput input)) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fun target hlarge hyes hrejects haccepts input =>
    run_fixedSelectorUniformProgram contracts clockDepth requestedRate body
      bodyBits bodyFuel target input _
      (bodyRun target hlarge hyes hrejects haccepts input)

/-! ## 3. Terminal fixed `hexecutes` -/

set_option maxHeartbeats 800000 in
-- The packaging bridge is bank agnostic once the uniform run is supplied.
/-- **The fixed schedule's `hexecutes`, with no diagonal premise.** -/
theorem fixed_hexecutes_of_selectorBank
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request : LanguageEvaluationRequest,
      fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits
          request ≤
        exponentialBudget exponent request.measure)
    (hfuel : ∀ request : LanguageEvaluationRequest,
      fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel
          request ≤
        exponentialBudget exponent request.measure)
    (hinitial : ∀ request : LanguageEvaluationRequest,
      natBitLength (max request.length request.code) ≤
        exponentialBudget exponent request.measure)
    (hrun : ∀ request : LanguageEvaluationRequest,
      runNPOracleProgram
          (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
          (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits
            request)
          (fixedSelectorUniformFuel contracts clockDepth requestedRate body
            bodyFuel request)
          (initialNPOracleState request.length request.code) =
        some (output request))
    (hboolean : ∀ request : LanguageEvaluationRequest, output request ≤ 1)
    (bodyRun : ∀ target
        (hlarge :
          fixedCaseOneTargetOnset contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
            target)
        (hyes :
          (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
            (sourceLength
              (fixedSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
                target))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
        (hrejects :
          ¬machine.toSemantic.accepts
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
        (haccepts :
          ∀ caseTwo : CanonicalAcceptingOracle
            (sizeBound := oracleSizeBound
              (fixedRequiredDegree contracts requestedRate))
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target),
            FixedCaseTwoAcceptance contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              (fixedSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
                target)
              caseTwo machine),
        ∀ input : BitInput target,
          runNPOracleProgram body (bodyBits ⟨target, input⟩)
              (bodyFuel ⟨target, input⟩)
              (initialNPOracleState target
                (selectorDrivenBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate)
                  (fixedSelectorChainIndex contracts clockDepth requestedRate
                    target)
                  (encodeBitInput input))) =
            some
              (fixedCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                requestedRate target hlarge hyes hrejects haccepts
                input).toNat) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
          target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (haccepts :
        ∀ caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)
            caseTwo machine),
      ∀ input : BitInput target,
        (executableLanguageProgramOfRun
            (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
            exponent hexponent
            (fixedSelectorUniformBits contracts clockDepth requestedRate
              bodyBits)
            (fixedSelectorUniformFuel contracts clockDepth requestedRate body
              bodyFuel)
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun
            (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
            exponent hexponent
            (fixedSelectorUniformBits contracts clockDepth requestedRate
              bodyBits)
            (fixedSelectorUniformFuel contracts clockDepth requestedRate body
              bodyFuel)
            output hbits hfuel hinitial hrun hboolean).request input) =
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_hexecutes_of_uniformTargetRun contracts clockDepth machine requestedRate
    (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
    exponent hexponent
    (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits)
    (fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel)
    output hbits hfuel hinitial hrun hboolean
    (fixed_huniform_of_selectorBank contracts clockDepth machine requestedRate
      body bodyBits bodyFuel bodyRun)

/-! ## 4. The headline-shaped one-totality interface -/

noncomputable def fixedSelectorExecutableLanguageProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (hbits : ∀ request : LanguageEvaluationRequest,
      fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits
          request ≤
        exponentialBudget exponent request.measure)
    (hfuel : ∀ request : LanguageEvaluationRequest,
      fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel
          request ≤
        exponentialBudget exponent request.measure)
    (hinitial : ∀ request : LanguageEvaluationRequest,
      natBitLength (max request.length request.code) ≤
        exponentialBudget exponent request.measure)
    (htotal :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedSelectorBodyFrame contracts clockDepth requestedRate)) :
    ExecutableLanguageProgram :=
  executableLanguageProgramOfRun
    (fixedSelectorUniformProgram contracts clockDepth requestedRate body)
    exponent hexponent
    (fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits)
    (fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel)
    (fixedSelectorTotalOutput contracts clockDepth requestedRate body bodyBits
      bodyFuel)
    hbits hfuel hinitial
    (fixedSelector_hrun_of_totalBody contracts clockDepth requestedRate body
      bodyBits bodyFuel htotal)
    (fixedSelector_hboolean_of_totalBody contracts clockDepth requestedRate body
      bodyBits bodyFuel htotal)

set_option maxHeartbeats 800000 in
-- Only the body semantics and the three resource premises remain.
/-- `hexecutes` from one total selector-frame body. -/
theorem fixed_hexecutes_of_selectorBodyTotal
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (hbits : ∀ request : LanguageEvaluationRequest,
      fixedSelectorUniformBits contracts clockDepth requestedRate bodyBits
          request ≤
        exponentialBudget exponent request.measure)
    (hfuel : ∀ request : LanguageEvaluationRequest,
      fixedSelectorUniformFuel contracts clockDepth requestedRate body bodyFuel
          request ≤
        exponentialBudget exponent request.measure)
    (hinitial : ∀ request : LanguageEvaluationRequest,
      natBitLength (max request.length request.code) ≤
        exponentialBudget exponent request.measure)
    (htotal :
      TotalBooleanRuns body bodyBits bodyFuel
        (fixedSelectorBodyFrame contracts clockDepth requestedRate))
    (bodyRun : ∀ target
        (hlarge :
          fixedCaseOneTargetOnset contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
            target)
        (hyes :
          (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
            (sourceLength
              (fixedSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
                target))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
        (hrejects :
          ¬machine.toSemantic.accepts
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
        (haccepts :
          ∀ caseTwo : CanonicalAcceptingOracle
            (sizeBound := oracleSizeBound
              (fixedRequiredDegree contracts requestedRate))
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target),
            FixedCaseTwoAcceptance contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              (fixedSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
                target)
              caseTwo machine),
        ∀ input : BitInput target,
          runNPOracleProgram body (bodyBits ⟨target, input⟩)
              (bodyFuel ⟨target, input⟩)
              (initialNPOracleState target
                (fixedSelectorBodyFrame contracts clockDepth requestedRate
                  ⟨target, input⟩)) =
            some
              (fixedCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                requestedRate target hlarge hyes hrejects haccepts
                input).toNat) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
          target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (haccepts :
        ∀ caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)
            caseTwo machine),
      ∀ input : BitInput target,
        (fixedSelectorExecutableLanguageProgram contracts clockDepth
            requestedRate body bodyBits bodyFuel exponent hexponent hbits hfuel
            hinitial htotal).runner.execute
          ((fixedSelectorExecutableLanguageProgram contracts clockDepth
            requestedRate body bodyBits bodyFuel exponent hexponent hbits hfuel
            hinitial htotal).request input) =
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_hexecutes_of_selectorBank contracts clockDepth machine requestedRate
    body bodyBits bodyFuel exponent hexponent
    (fixedSelectorTotalOutput contracts clockDepth requestedRate body bodyBits
      bodyFuel)
    hbits hfuel hinitial
    (fixedSelector_hrun_of_totalBody contracts clockDepth requestedRate body
      bodyBits bodyFuel htotal)
    (fixedSelector_hboolean_of_totalBody contracts clockDepth requestedRate body
      bodyBits bodyFuel htotal)
    bodyRun

end NearCubicWires.FixedSelectorHexecutes

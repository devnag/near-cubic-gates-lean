import Proof.Circuits.InverseLengthStage

/-!
# The inverse schedule's `hexecutes`, from the selector-driven bank

`ScheduleDiagonalObstruction` / `ScheduleImageDiagonalObstruction` proved every
form of `hdiagonal` unsatisfiable; `SourceDrivenNumeralBank` replaced the
log-decoding bank with the selector-driven bank whose frame is the chain's own
frame definitionally; and `InverseLengthStage.inverse_scheduledLengthRuns` made
its one residual a theorem.  This module closes the seam: it produces the
executable target language's terminal obligation `hexecutes` from the
selector-driven bank, with **no `hdiagonal` in any form**.

`ExecutableTargetLanguagePackaging.inverse_hexecutes_of_uniformTargetRun` is bank
agnostic — it consumes an arbitrary `program` with a totality premise (`hrun`)
and an on-onset canonical premise (`huniform`).  §1 links the selector-driven
bank in front of a register-driven body; §2 derives `huniform` from a body that
returns the canonical target from the **selector-driven frame**
(`selectorDrivenBankFrame`), i.e. the chain's own frame; §3 packages the two
into `hexecutes`.

## What is carried, and why it is no longer `hdiagonal`

The remaining premise is `bodyRun`, at `selectorDrivenBankFrame` rather than at
the old `publishedBankFrame … target`.  This is not `hdiagonal`: the selector
bank *builds* the chain's frame, so the body reads the chain's numerals
unconditionally.  `SelectorDrivenAtomContext.inverseAtomContext_ofSelectorRegisters`
is the exemplar showing the register identification the old body needed the
diagonal for is now definitional.  Discharging `bodyRun` in full is the body
chain's own restatement at the selector frame — the industrialized replay named
at the end of this file.
-/

namespace NearCubicWires.InverseSelectorHexecutes

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.ScheduledRecovery
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The selector-driven uniform target program -/

/-- The selector-driven bank at the published inverse parameters, in front of a
register-driven body. -/
noncomputable def selectorUniformProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (body : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (publishedSourceDrivenBankProgram
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthProgram contracts clockDepth advantageExponent))
    body

/-- The chain's own source index at one target. -/
noncomputable def selectorChainIndex
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (target : ℕ) : ℕ :=
  inverseSourceIndex
    (inverseSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseCoreAdvantagePower advantageExponent) target)

noncomputable def selectorUniformBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (bodyBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (publishedSourceDrivenBankBits
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (LanguageEvaluationRequest.length request)
      (inverseLengthBits contracts clockDepth advantageExponent request)
      (inverseScheduleLength contracts clockDepth advantageExponent
        (LanguageEvaluationRequest.length request))
      (LanguageEvaluationRequest.code request))
    (bodyBits request)

noncomputable def selectorUniformFuel
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (body : NPOracleProgram) (bodyFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel body
    (publishedSourceDrivenBankFuel
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthFuel contracts clockDepth advantageExponent request)
      (inverseScheduleLength contracts clockDepth advantageExponent
        (LanguageEvaluationRequest.length request)))
    (bodyFuel request)

/-- **The linked stream, executed.**  Whatever the register-driven body returns
from the selector-driven frame, the linked stream returns from the request. -/
theorem run_selectorUniformProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
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
              (inverseBankRate contracts advantageExponent)
              (selectorChainIndex contracts clockDepth advantageExponent target)
              (encodeBitInput input))) =
        some value) :
    runNPOracleProgram
        (selectorUniformProgram contracts clockDepth advantageExponent body)
        (selectorUniformBits contracts clockDepth advantageExponent bodyBits
          ⟨target, input⟩)
        (selectorUniformFuel contracts clockDepth advantageExponent body bodyFuel
          ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some value :=
  run_occurrenceStage
    (run_inverseSelectorDrivenBankProgram contracts clockDepth advantageExponent
      (inverseLengthProgram contracts clockDepth advantageExponent)
      (inverseLengthBits contracts clockDepth advantageExponent)
      (inverseLengthFuel contracts clockDepth advantageExponent)
      (inverse_scheduledLengthRuns contracts clockDepth advantageExponent)
      target input)
    hbody

/-! ## 2. `huniform` from a selector-frame body -/

/-- **`huniform` for the selector-driven bank.**  From a body that returns the
canonical target from the selector-driven frame, the linked stream returns it
from the request. -/
theorem inverse_huniform_of_selectorBank
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (bodyRun : ∀ target
        (hlarge :
          inverseCaseOneTargetOnset contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            advantageExponent ≤ target)
        (hyes :
          (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
            (sourceLength (inverseSourceIndex
              (inverseSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent) target)))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))
        (hrejects :
          ¬machine.toSemantic.accepts
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))
        (haccepts :
          ∀ caseTwo : CanonicalAcceptingOracle
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
              caseTwo machine),
        ∀ input : BitInput target,
          runNPOracleProgram body (bodyBits ⟨target, input⟩)
              (bodyFuel ⟨target, input⟩)
              (initialNPOracleState target
                (selectorDrivenBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent)
                  (selectorChainIndex contracts clockDepth advantageExponent
                    target)
                  (encodeBitInput input))) =
            some
              (inverseCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target hlarge hyes hrejects haccepts
                input).toNat) :
    ∀ target
      (hlarge :
        inverseCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          advantageExponent ≤ target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
      (haccepts :
        ∀ caseTwo : CanonicalAcceptingOracle
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
            caseTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram
            (selectorUniformProgram contracts clockDepth advantageExponent body)
            (selectorUniformBits contracts clockDepth advantageExponent bodyBits
              ⟨target, input⟩)
            (selectorUniformFuel contracts clockDepth advantageExponent body
              bodyFuel ⟨target, input⟩)
            (initialNPOracleState target (encodeBitInput input)) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts
              input).toNat :=
  fun target hlarge hyes hrejects haccepts input =>
    run_selectorUniformProgram contracts clockDepth advantageExponent body
      bodyBits bodyFuel target input _
      (bodyRun target hlarge hyes hrejects haccepts input)

/-! ## 3. `hexecutes` from the selector-driven bank -/

set_option maxHeartbeats 800000 in
-- The bank-agnostic packaging bridge is applied to the selector-driven stream.
/-- **The inverse schedule's `hexecutes`, from the selector-driven bank.**  The
executable target language's terminal obligation, with `hdiagonal` GONE: the
only body premise is `bodyRun` at the selector-driven frame, which the bank
builds definitionally. -/
theorem inverse_hexecutes_of_selectorBank
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      selectorUniformBits contracts clockDepth advantageExponent bodyBits
          request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      selectorUniformFuel contracts clockDepth advantageExponent body bodyFuel
          request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram
          (selectorUniformProgram contracts clockDepth advantageExponent body)
          (selectorUniformBits contracts clockDepth advantageExponent bodyBits
            request)
          (selectorUniformFuel contracts clockDepth advantageExponent body
            bodyFuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
    (bodyRun : ∀ target
        (hlarge :
          inverseCaseOneTargetOnset contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            advantageExponent ≤ target)
        (hyes :
          (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
            (sourceLength (inverseSourceIndex
              (inverseSelectedSource contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseCoreAdvantagePower advantageExponent) target)))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))
        (hrejects :
          ¬machine.toSemantic.accepts
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))
        (haccepts :
          ∀ caseTwo : CanonicalAcceptingOracle
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
              caseTwo machine),
        ∀ input : BitInput target,
          runNPOracleProgram body (bodyBits ⟨target, input⟩)
              (bodyFuel ⟨target, input⟩)
              (initialNPOracleState target
                (selectorDrivenBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent)
                  (selectorChainIndex contracts clockDepth advantageExponent
                    target)
                  (encodeBitInput input))) =
            some
              (inverseCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target hlarge hyes hrejects haccepts
                input).toNat) :
    ∀ target
      (hlarge :
        inverseCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          advantageExponent ≤ target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target)))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target))
      (haccepts :
        ∀ caseTwo : CanonicalAcceptingOracle
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
            caseTwo machine),
      ∀ input : BitInput target,
        (executableLanguageProgramOfRun
            (selectorUniformProgram contracts clockDepth advantageExponent body)
            exponent hexponent
            (selectorUniformBits contracts clockDepth advantageExponent bodyBits)
            (selectorUniformFuel contracts clockDepth advantageExponent body
              bodyFuel)
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun
            (selectorUniformProgram contracts clockDepth advantageExponent body)
            exponent hexponent
            (selectorUniformBits contracts clockDepth advantageExponent bodyBits)
            (selectorUniformFuel contracts clockDepth advantageExponent body
              bodyFuel)
            output hbits hfuel hinitial hrun hboolean).request input) =
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts
            input).toNat :=
  inverse_hexecutes_of_uniformTargetRun contracts clockDepth machine
    advantageExponent
    (selectorUniformProgram contracts clockDepth advantageExponent body)
    exponent hexponent
    (selectorUniformBits contracts clockDepth advantageExponent bodyBits)
    (selectorUniformFuel contracts clockDepth advantageExponent body bodyFuel)
    output hbits hfuel hinitial hrun hboolean
    (inverse_huniform_of_selectorBank contracts clockDepth machine
      advantageExponent body bodyBits bodyFuel bodyRun)

end NearCubicWires.InverseSelectorHexecutes

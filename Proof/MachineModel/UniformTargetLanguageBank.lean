import Proof.MachineModel.ExecutableTargetLanguagePackaging
import Proof.MachineModel.RuntimeScheduleNumeralBank

namespace NearCubicWires.UniformTargetLanguageBank

open NearCubicWires
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The linked stream -/

/-- The numeral bank at the published parameters of one hierarchy outer PCP and
one pointwise PCPP source. -/
noncomputable def publishedBankProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ) : NPOracleProgram :=
  scheduleNumeralBankProgram outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1)

/-- The bank's frame at one request: every target-derived numeral in a
register, beside the retained point code. -/
noncomputable def publishedBankFrame
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate inputLength code : ℕ) :
    ℕ :=
  scheduleNumeralBankOutput (bankSourceLength inputLength)
    (scheduledWidth outer (sourceIndexOfLength inputLength))
    (outer.pcp.queryCount (bankSourceLength inputLength))
    (inverseCopies outer pcppSource rate (sourceIndexOfLength inputLength))
    code

noncomputable def publishedBankFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate inputLength : ℕ) : ℕ :=
  scheduleNumeralBankFuel outer.pcp.shape.program clockDepth
    outer.pcp.shape.coefficient outer.proofExponent
    (recoveryBlock pcppSource * rate) (recoveryBlock pcppSource + 1) inputLength
    (outer.pcp.shape.budget (bankSourceLength inputLength))

noncomputable def publishedBankBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate inputLength code : ℕ) :
    ℕ :=
  scheduleNumeralBankBits clockDepth outer.pcp.shape.coefficient
    outer.proofExponent (recoveryBlock pcppSource * rate)
    (recoveryBlock pcppSource + 1) inputLength code
    (outer.pcp.shape.budget (bankSourceLength inputLength))
    (outer.pcp.shape.execute (bankSourceLength inputLength))

/-- **The uniform target program.**  One instruction stream for every request:
the published numeral bank, then the register-driven dispatched target. -/
noncomputable def uniformTargetProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (body : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (publishedBankProgram outer pcppSource rate) body

noncomputable def uniformTargetBits
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (bodyBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (publishedBankBits outer pcppSource rate
      (LanguageEvaluationRequest.length request)
      (LanguageEvaluationRequest.code request))
    (bodyBits request)

noncomputable def uniformTargetFuel
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (body : NPOracleProgram) (bodyFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel body
    (publishedBankFuel outer pcppSource rate
      (LanguageEvaluationRequest.length request))
    (bodyFuel request)

/-- **The linked stream, executed.**  Whatever the register-driven body returns
from the bank's frame, the linked stream returns from the request itself. -/
theorem run_uniformTargetProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (target : ℕ) (input : BitInput target) (value : ℕ)
    (hbody :
      runNPOracleProgram body (bodyBits ⟨target, input⟩)
          (bodyFuel ⟨target, input⟩)
          (initialNPOracleState target
            (publishedBankFrame outer pcppSource rate target
              (encodeBitInput input))) =
        some value) :
    runNPOracleProgram (uniformTargetProgram outer pcppSource rate body)
        (uniformTargetBits outer pcppSource rate bodyBits ⟨target, input⟩)
        (uniformTargetFuel outer pcppSource rate body bodyFuel ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some value :=
  run_occurrenceStage
    (run_publishedScheduleNumeralBankProgram outer pcppSource rate target
      (encodeBitInput input))
    hbody

/-! ## 2. The inverse schedule's `huniform` and `hexecutes` -/

/-- The inverse schedule's numeral-bank rate. -/
noncomputable def inverseBankRate
    (contracts : PublishedContracts) (advantageExponent : ℝ) : ℕ :=
  inverseRate contracts (inverseCoreAdvantagePower advantageExponent)

set_option maxHeartbeats 400000 in
-- The bank is discharged once and for all; only the body premise is consumed.
/-- **The inverse schedule's `huniform`, from the register-driven body.**  This
is the premise `inverse_hexecutes_of_uniformTargetRun` consumes, verbatim. -/
theorem inverse_huniform_of_bodyRun
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
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
            (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent) body)
            (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent) bodyBits
              ⟨target, input⟩)
            (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent) body bodyFuel
              ⟨target, input⟩)
            (initialNPOracleState target (encodeBitInput input)) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts
              input).toNat :=
  fun target hlarge hyes hrejects haccepts input =>
    run_uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) body bodyBits bodyFuel
      target input _
      (bodyRun target hlarge hyes hrejects haccepts input)

/-! ## 3. The fixed schedule's `huniform` -/

/-- The fixed schedule's numeral-bank rate.  The fixed copy count is itself a
frozen numeral — `RecoveryScheduleEnvelope.fixedCopies` does not depend on the
scheduled width — so on this schedule the bank's copy register is redundant and
the body may ignore it. -/
noncomputable def fixedBankRate
    (contracts : PublishedContracts) (requestedRate : ℕ) : ℕ :=
  fixedRate contracts requestedRate

set_option maxHeartbeats 400000 in
-- The bank is discharged once and for all; only the body premise is consumed.
/-- **The fixed schedule's `huniform`, from the register-driven body.** -/
theorem fixed_huniform_of_bodyRun
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
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
            (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (fixedBankRate contracts requestedRate) body)
            (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (fixedBankRate contracts requestedRate) bodyBits ⟨target, input⟩)
            (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (fixedBankRate contracts requestedRate) body bodyFuel
              ⟨target, input⟩)
            (initialNPOracleState target (encodeBitInput input)) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fun target hlarge hyes hrejects haccepts input =>
    run_uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate) body bodyBits bodyFuel target
      input _ (bodyRun target hlarge hyes hrejects haccepts input)

/-! ## 4. `hexecutes`, modulo the register-driven body -/

set_option maxHeartbeats 800000 in
-- The packaging bridge is applied to the linked stream; the body premise is
-- passed through untouched.
/-- **The inverse schedule's `hexecutes`, from the register-driven body.**  The
executable target language's terminal obligation is discharged for the linked
stream `bank ⊕ body`: nothing separates the published closure from the chains
except `bodyRun`, one statement about one program at one frame. -/
theorem inverse_hexecutes_of_bodyRun
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) bodyBits) request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body bodyFuel) request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram
          (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body)
          ((uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) bodyBits) request)
          ((uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body bodyFuel) request)
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
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
            (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body)
            exponent hexponent
            (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) bodyBits)
            (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body bodyFuel)
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun
            (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body)
            exponent hexponent
            (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) bodyBits)
            (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body bodyFuel)
            output hbits hfuel hinitial hrun hboolean).request input) =
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts
            input).toNat :=
  inverse_hexecutes_of_uniformTargetRun contracts clockDepth machine
    advantageExponent
    (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body)
    exponent hexponent
    (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) bodyBits)
    (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) body bodyFuel)
    output hbits hfuel hinitial hrun hboolean
    (inverse_huniform_of_bodyRun contracts clockDepth machine advantageExponent
      body bodyBits bodyFuel bodyRun)

set_option maxHeartbeats 800000 in
-- The packaging bridge is applied to the linked stream; the body premise is
-- passed through untouched.
/-- **The fixed schedule's `hexecutes`, from the register-driven body.** -/
theorem fixed_hexecutes_of_bodyRun
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (body : NPOracleProgram)
    (bodyBits bodyFuel : LanguageEvaluationRequest → ℕ)
    (exponent : ℕ) (hexponent : 0 < exponent)
    (output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) bodyBits) request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body bodyFuel) request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram
          (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body)
          ((uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) bodyBits) request)
          ((uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body bodyFuel) request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
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
            (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body)
            exponent hexponent
            (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) bodyBits)
            (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body bodyFuel)
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun
            (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body)
            exponent hexponent
            (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) bodyBits)
            (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body bodyFuel)
            output hbits hfuel hinitial hrun hboolean).request input) =
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_hexecutes_of_uniformTargetRun contracts clockDepth machine requestedRate
    (uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body)
    exponent hexponent
    (uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) bodyBits)
    (uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) body bodyFuel)
    output hbits hfuel hinitial hrun hboolean
    (fixed_huniform_of_bodyRun contracts clockDepth machine requestedRate body
      bodyBits bodyFuel bodyRun)

/-! ## 5. The bank's frame on the scheduled diagonal

At a request whose public length is the scheduled source length, the frame the
body reads is literally the chain's own numerals at that source index.  This is
the identity a register-driven body applies before dispatching.
-/

theorem publishedBankFrame_at_sourceLength
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource) (rate sourceIndex code : ℕ) :
    publishedBankFrame outer pcppSource rate (sourceLength sourceIndex) code =
      scheduleNumeralBankOutput (sourceLength sourceIndex)
        (scheduledWidth outer sourceIndex)
        (outer.pcp.queryCount (sourceLength sourceIndex))
        (inverseCopies outer pcppSource rate sourceIndex) code := by
  rw [publishedBankFrame, bankSourceLength_sourceLength,
    sourceIndexOfLength_sourceLength]

end NearCubicWires.UniformTargetLanguageBank

import Proof.MachineModel.LanguageScheduleDecoderProgram

namespace NearCubicWires.ExecutableTargetLanguagePackaging

open NearCubicWires
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The packaging bridge -/

/-- The certified output of a packaged run is the value the run theorem
returns.  This is the only step that crosses the `ExponentialNatProgram`
boundary. -/
theorem output_eq_of_run
    (program : NPOracleProgram)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (target : ℕ) (input : BitInput target) (value : ℕ)
    (hagree :
      runNPOracleProgram program (bits ⟨target, input⟩) (fuel ⟨target, input⟩)
          (initialNPOracleState target (encodeBitInput input)) = some value) :
    output ⟨target, input⟩ = value := by
  have hpacked := hrun ⟨target, input⟩
  exact (Option.some.inj (hagree.symm.trans hpacked)).symm

/-! ## 2. The inverse schedule's `hexecutes` -/

/-- **The inverse schedule's `hexecutes`, from the per-request output.**  The
statement is the one `PublishedRecoveryClosure` consumes, with the published
clock depth left as a parameter so that the closure may instantiate it at
`machine.verifier.degree + 1`. -/
theorem inverse_hexecutes_of_canonicalOutput
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      bits request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      fuel request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
    (hcanonical : ∀ target
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
          output ⟨target, input⟩ =
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
        (executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).request input) =
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts
            input).toNat := by
  intro target hlarge hyes hrejects haccepts input
  have hexecute :=
    executableLanguageProgramOfRun_execute program exponent hexponent bits fuel
      output hbits hfuel hinitial hrun hboolean
      (⟨target, input⟩ : LanguageEvaluationRequest)
  exact hexecute.trans (hcanonical target hlarge hyes hrejects haccepts input)

theorem inverse_hexecutes_of_uniformTargetRun
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      bits request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      fuel request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
    (huniform : ∀ target
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
          runNPOracleProgram program (bits ⟨target, input⟩)
              (fuel ⟨target, input⟩)
              (initialNPOracleState target (encodeBitInput input)) =
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
        (executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).request input) =
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts
            input).toNat :=
  inverse_hexecutes_of_canonicalOutput contracts clockDepth machine
    advantageExponent program exponent hexponent bits fuel output hbits hfuel
    hinitial hrun hboolean
    (fun target hlarge hyes hrejects haccepts input =>
      output_eq_of_run program bits fuel output hrun target input _
        (huniform target hlarge hyes hrejects haccepts input))

/-! ## 3. The fixed schedule's `hexecutes` -/

/-- Fixed-rate counterpart of `inverse_hexecutes_of_canonicalOutput`. -/
theorem fixed_hexecutes_of_canonicalOutput
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      bits request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      fuel request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
    (hcanonical : ∀ target
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
          output ⟨target, input⟩ =
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts input).toNat) :
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
        (executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).request input) =
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat := by
  intro target hlarge hyes hrejects haccepts input
  have hexecute :=
    executableLanguageProgramOfRun_execute program exponent hexponent bits fuel
      output hbits hfuel hinitial hrun hboolean
      (⟨target, input⟩ : LanguageEvaluationRequest)
  exact hexecute.trans (hcanonical target hlarge hyes hrejects haccepts input)

/-- Fixed-rate counterpart of `inverse_hexecutes_of_uniformTargetRun`. -/
theorem fixed_hexecutes_of_uniformTargetRun
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      bits request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      fuel request ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
    (huniform : ∀ target
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
          runNPOracleProgram program (bits ⟨target, input⟩)
              (fuel ⟨target, input⟩)
              (initialNPOracleState target (encodeBitInput input)) =
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
        (executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).runner.execute
          ((executableLanguageProgramOfRun program exponent hexponent bits fuel
            output hbits hfuel hinitial hrun hboolean).request input) =
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_hexecutes_of_canonicalOutput contracts clockDepth machine requestedRate
    program exponent hexponent bits fuel output hbits hfuel hinitial hrun
    hboolean
    (fun target hlarge hyes hrejects haccepts input =>
      output_eq_of_run program bits fuel output hrun target input _
        (huniform target hlarge hyes hrejects haccepts input))

end NearCubicWires.ExecutableTargetLanguagePackaging

import Proof.MachineModel.BankDispatchedTargetBody
import Proof.MachineModel.EmittedBranchTargetProgram

namespace NearCubicWires.BankEmittedBranchSelector

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The emitter premise at the bank's frame -/

/-- **The one selector-side hypothesis.**  At every onset-large request the
emitter, started on the numeral bank's frame, returns the tagged
inverse-schedule atom stream beside that same frame.  Nothing else about the
emitter is used, and the dispatched body never queries a target below the
Case-1 onset. -/
def InverseEmitterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitter : NPOracleProgram)
    (emitterBits emitterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram emitter (emitterBits ⟨target, input⟩)
        (emitterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input))) =
      some
        (Nat.pair
          (encodeTaggedList
            (inverseSelectorAtoms contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input)))

/-! ## 2. The selector's resource envelopes at the bank's frame -/

noncomputable def inverseBankSelectorBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitterBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  emittedBranchSelectorBits
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent (LanguageEvaluationRequest.length request))
    (oracleSizeBound
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent)
            (LanguageEvaluationRequest.length request)))))
    (LanguageEvaluationRequest.length request)
    (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (LanguageEvaluationRequest.length request)
      (LanguageEvaluationRequest.code request))
    (emitterBits request)

noncomputable def inverseBankSelectorFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitterFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  emittedBranchSelectorFuel
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent (LanguageEvaluationRequest.length request))
    (oracleSizeBound
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent)
            (LanguageEvaluationRequest.length request)))))
    (emitterFuel request)

/-! ## 3. `bodyRun` from the emitter premise and the two chains -/

/-- **The inverse schedule's `bodyRun`, selector side closed.**  The two
selector premises of `BankDispatchedTargetBody.inverse_bodyRun_of_dispatch` are
discharged from `InverseEmitterRuns`; the two chain premises pass through
unchanged.  No recovery-code immediate and no branch-query immediate remains in
the dispatched stream. -/
theorem inverse_bodyRun_of_emitterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitter caseOne caseTwo : NPOracleProgram)
    (emitterBits emitterFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hemitter :
      InverseEmitterRuns contracts clockDepth machine advantageExponent emitter
        emitterBits emitterFuel)
    (hchainOne : ∀ target
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
              branchTwo machine)
        (data : ScheduledCaseOneData
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedAmplifier contracts)
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target)),
        inverseTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hyes = .caseOne data →
        ∀ input : BitInput target,
          runNPOracleProgram caseOne (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
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
                input).toNat)
    (hchainTwo : ∀ target
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
              branchTwo machine)
        (branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target)),
        inverseTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hyes = .caseTwo branchTwo →
        ∀ input : BitInput target,
          runNPOracleProgram caseTwo (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
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
        runNPOracleProgram
            (bankDispatchedBodyProgram (emittedBranchSelectorProgram emitter)
              caseOne caseTwo)
            (bankDispatchedBodyBits contracts clockDepth advantageExponent
              (inverseBankSelectorBits contracts clockDepth machine
                advantageExponent emitterBits)
              chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo
              (inverseBankSelectorFuel contracts clockDepth machine
                advantageExponent emitterFuel)
              chainFuel ⟨target, input⟩)
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
              input).toNat :=
  inverse_bodyRun_of_dispatch contracts clockDepth machine advantageExponent
    (emittedBranchSelectorProgram emitter) caseOne caseTwo
    (inverseBankSelectorBits contracts clockDepth machine advantageExponent
      emitterBits)
    (inverseBankSelectorFuel contracts clockDepth machine advantageExponent
      emitterFuel)
    chainBits chainFuel
    (fun target hlarge _hyes data _hbranch input =>
      run_emittedBranchSelectorProgram_caseOne data target
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target
          (encodeBitInput input))
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target
          (encodeBitInput input))
        (emitterBits ⟨target, input⟩) (emitterFuel ⟨target, input⟩) emitter
        (hemitter target hlarge input))
    (fun target hlarge _hyes branchTwo _hbranch input =>
      run_emittedBranchSelectorProgram_caseTwo branchTwo target
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target
          (encodeBitInput input))
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target
          (encodeBitInput input))
        (emitterBits ⟨target, input⟩) (emitterFuel ⟨target, input⟩) emitter
        (hemitter target hlarge input))
    hchainOne hchainTwo

end NearCubicWires.BankEmittedBranchSelector

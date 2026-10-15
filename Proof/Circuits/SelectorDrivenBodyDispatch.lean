import Proof.Circuits.SelectorDrivenEmitterRuns

/-!
# The dispatched bodyRun at an abstract bank frame

Site B-2b of the body-chain replay, stated generically over an abstract frame
function `pointCode`.  The base branch-target run lemmas take the bank frame as
an opaque point code, so these are the frozen proofs of
`BankDispatchedTargetBody.inverse_bodyRun_of_dispatch` /
`BankEmittedBranchSelector.inverse_bodyRun_of_emitterRuns` with the frame kept
abstract — which both avoids the expensive `whnf` on a concrete selector frame
and yields a single lemma reusable at the selector frame.  The selector
schedule's chains are carried as premises.  No `hdiagonal`.
-/

namespace NearCubicWires.SelectorDrivenBodyDispatch

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenEmitterRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private branchTargetBitBits_mono_output from
  Proof.MachineModel.BankDispatchedTargetBody

/-! ## 1. The dispatch width at an opaque frame

The frozen bank body's width mentions `publishedBankFrame`.  That envelope
cannot type a run begun at a different frame: `branchTargetBitBits` charges the
bit length of the retained point code.  Keep the same two-branch maximum, but
parameterize that point code explicitly for the selector-driven replay. -/

noncomputable def bankDispatchedBodyBitsAtFrame
    (pointCode : LanguageEvaluationRequest → ℕ)
    (selectorBits chainBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (branchTargetBitBits (LanguageEvaluationRequest.length request) 0
      (pointCode request) (selectorBits request) (chainBits request) 1)
    (branchTargetBitBits (LanguageEvaluationRequest.length request) 1
      (pointCode request) (selectorBits request) (chainBits request) 1)

/-- The emitted selector's exact width when both its request code and retained
point code are the supplied opaque frame.  Its frozen inverse wrapper charges
`publishedBankFrame`, so it cannot be reused at the selector-driven frame. -/
noncomputable def inverseBankSelectorBitsAtFrame
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pointCode : LanguageEvaluationRequest → ℕ)
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
    (pointCode request) (emitterBits request)

set_option maxHeartbeats 1600000 in
-- The branch proof elaborates two large schedule-dependent canonical outputs.
theorem inverse_bodyRun_of_dispatch_atFrame
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pointCode : LanguageEvaluationRequest → ℕ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hselectorOne : ∀ target
        (_hlarge :
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
          runNPOracleProgram selector (selectorBits ⟨target, input⟩)
              (selectorFuel ⟨target, input⟩)
              (initialNPOracleState target
                (pointCode ⟨target, input⟩)) =
            some
              (Nat.pair 0
                (pointCode ⟨target, input⟩)))
    (hselectorTwo : ∀ target
        (_hlarge :
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
          runNPOracleProgram selector (selectorBits ⟨target, input⟩)
              (selectorFuel ⟨target, input⟩)
              (initialNPOracleState target
                (pointCode ⟨target, input⟩)) =
            some
              (Nat.pair 1
                (pointCode ⟨target, input⟩)))
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
                (pointCode ⟨target, input⟩)) =
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
                (pointCode ⟨target, input⟩)) =
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
        runNPOracleProgram (bankDispatchedBodyProgram selector caseOne caseTwo)
            (bankDispatchedBodyBitsAtFrame pointCode selectorBits chainBits
              ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo selectorFuel chainFuel
              ⟨target, input⟩)
            (initialNPOracleState target
              (pointCode ⟨target, input⟩)) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts
              input).toNat := by
  intro target hlarge hyes hrejects haccepts input
  have houtput :
      (inverseCanonicalTargetFunction contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target hlarge hyes hrejects haccepts input).toNat ≤
        1 := by
    cases (inverseCanonicalTargetFunction contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hlarge hyes hrejects haccepts input) <;>
      simp
  cases hbranch :
      inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
  | caseOne data =>
      have hrun :=
        run_branchTargetBitProgram_caseOne selector caseOne caseTwo target
          (pointCode ⟨target, input⟩)
          (selectorBits ⟨target, input⟩) (selectorFuel ⟨target, input⟩)
          (chainBits ⟨target, input⟩) (chainFuel ⟨target, input⟩)
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts input).toNat
          (hselectorOne target hlarge hyes data hbranch input)
          (hchainOne target hlarge hyes hrejects haccepts data hbranch input)
      exact run_bits_mono hrun
        ((branchTargetBitBits_mono_output
            (inputLength := target) (tag := 0)
            (pointCode := pointCode ⟨target, input⟩)
            (selectorBits := selectorBits ⟨target, input⟩)
            (chainBits := chainBits ⟨target, input⟩)
            (output :=
              (inverseCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target hlarge hyes hrejects haccepts
                input).toNat)
            houtput).trans
          (Nat.le_max_left _ _))
  | caseTwo branchTwo =>
      have hrun :=
        run_branchTargetBitProgram_caseTwo selector caseOne caseTwo target
          (pointCode ⟨target, input⟩)
          1 (selectorBits ⟨target, input⟩) (selectorFuel ⟨target, input⟩)
          (chainBits ⟨target, input⟩) (chainFuel ⟨target, input⟩)
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts input).toNat
          Nat.one_ne_zero
          (hselectorTwo target hlarge hyes branchTwo hbranch input)
          (hchainTwo target hlarge hyes hrejects haccepts branchTwo hbranch
            input)
      exact run_bits_mono hrun
        ((branchTargetBitBits_mono_output
            (inputLength := target) (tag := 1)
            (pointCode := pointCode ⟨target, input⟩)
            (selectorBits := selectorBits ⟨target, input⟩)
            (chainBits := chainBits ⟨target, input⟩)
            (output :=
              (inverseCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target hlarge hyes hrejects haccepts
                input).toNat)
            houtput).trans
          (Nat.le_max_right _ _))

/-! ## 4. Chaining to `hexecutes`

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` applied to
`bankDispatchedBodyProgram selector caseOne caseTwo`, its width
`bankDispatchedBodyBits`, its fuel `bankDispatchedBodyFuel`, and the `bodyRun`
of §3 discharges the executable target language's terminal obligation for the
linked stream `bank ⊕ dispatcher`; the packaging's own resource premises
(`hbits`, `hfuel`, `hinitial`, `hrun`, `hboolean`) pass through untouched.
-/

set_option maxHeartbeats 1600000 in
-- The wrapper specializes the full dispatch contract at two dependent branches.
theorem inverse_bodyRun_of_emitterRuns_atFrame
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pointCode : LanguageEvaluationRequest → ℕ)
    (emitter caseOne caseTwo : NPOracleProgram)
    (emitterBits emitterFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hemitter : ∀ (target : ℕ)
        (_hlarge :
          inverseCaseOneTargetOnset contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            advantageExponent ≤ target)
        (input : BitInput target),
        runNPOracleProgram emitter (emitterBits ⟨target, input⟩)
            (emitterFuel ⟨target, input⟩)
            (initialNPOracleState target (pointCode ⟨target, input⟩)) =
          some
            (Nat.pair
              (encodeTaggedList
                (inverseSelectorAtoms contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target))
              (pointCode ⟨target, input⟩)))
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
                (pointCode ⟨target, input⟩)) =
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
                (pointCode ⟨target, input⟩)) =
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
            (bankDispatchedBodyBitsAtFrame pointCode
              (inverseBankSelectorBitsAtFrame contracts clockDepth machine
                advantageExponent pointCode emitterBits)
              chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo
              (inverseBankSelectorFuel contracts clockDepth machine
                advantageExponent emitterFuel)
              chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (pointCode ⟨target, input⟩)) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts
              input).toNat :=
  inverse_bodyRun_of_dispatch_atFrame contracts clockDepth machine advantageExponent
    pointCode (emittedBranchSelectorProgram emitter) caseOne caseTwo
    (inverseBankSelectorBitsAtFrame contracts clockDepth machine
      advantageExponent pointCode emitterBits)
    (inverseBankSelectorFuel contracts clockDepth machine advantageExponent
      emitterFuel)
    chainBits chainFuel
    (fun target hlarge _hyes data _hbranch input =>
      run_emittedBranchSelectorProgram_caseOne data target
        (pointCode ⟨target, input⟩)
        (pointCode ⟨target, input⟩)
        (emitterBits ⟨target, input⟩) (emitterFuel ⟨target, input⟩) emitter
        (hemitter target hlarge input))
    (fun target hlarge _hyes branchTwo _hbranch input =>
      run_emittedBranchSelectorProgram_caseTwo branchTwo target
        (pointCode ⟨target, input⟩)
        (pointCode ⟨target, input⟩)
        (emitterBits ⟨target, input⟩) (emitterFuel ⟨target, input⟩) emitter
        (hemitter target hlarge input))
    hchainOne hchainTwo

end NearCubicWires.SelectorDrivenBodyDispatch

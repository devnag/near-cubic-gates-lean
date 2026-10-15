import Proof.MachineModel.BankCaseTwoSeedBlockListProgram

/-!
# The register-driven body: one branch dispatcher over the bank's frame

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` consumes exactly one
premise about one fixed instruction stream: `bodyRun`, the statement that at
every requested target the body, started on the numeral bank's frame, returns
the canonical target bit.

`BranchTargetLanguageProgram.branchTargetBitProgram` is *frame agnostic*: the
selector consumes the request code and returns `pair tag code`, and the chosen
chain is then started on the *same* code.  Instantiating that code with the
numeral bank's frame therefore produces a body of exactly the required shape,
with no target-derived immediate contributed by the dispatcher itself.

This module performs that instantiation and discharges `bodyRun` from four
named premises — the selector's two tags and the two chains' values, each
stated at the bank's frame.  §3 records the two premises that are already
inhabited by this fleet's register-driven stages:

* the Case-2 chain is `BankCaseTwoSeedBlockListProgram.bankCaseTwoTargetBitProgram`,
  whose run at the bank's frame is
  `run_bankCaseTwoTargetBitProgram_inverse` (modulo the per-block occurrence
  callee and the diagonal);
* the selector is
  `BankRecoveryCodeProgram.emittedBranchSelectorProgram`, whose two tag lemmas
  `run_emittedBranchSelectorProgram_caseOne/caseTwo` take the retained code —
  here the bank's frame — as a parameter.

The two premises that remain open at the time of writing are the Case-1
chain's value at the bank's frame and the structural atom emitter's run; both
are named, and neither is a property of the dispatcher.
-/

namespace NearCubicWires.BankDispatchedTargetBody

open NearCubicWires
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping for the dispatcher -/

private theorem branchTargetBitBits_mono_output
    (inputLength tag pointCode selectorBits chainBits output : ℕ)
    (houtput : output ≤ 1) :
    branchTargetBitBits inputLength tag pointCode selectorBits chainBits
        output ≤
      branchTargetBitBits inputLength tag pointCode selectorBits chainBits 1 :=
  max_le_max (Nat.le_refl _)
    (max_le_max (Nat.le_refl _)
      (max_le_max (Nat.le_refl _)
        (max_le_max (Nat.le_refl _) (natBitLength_mono houtput))))

/-! ## 2. The body and its resource envelopes -/

/-- **The register-driven body.**  One branch dispatcher; every stage reads the
numeral bank's frame. -/
def bankDispatchedBodyProgram (selector caseOne caseTwo : NPOracleProgram) :
    NPOracleProgram :=
  branchTargetBitProgram selector caseOne caseTwo

/-- The dispatcher's width at one request: the two admissible tags, at the
only two admissible outputs of a target *bit*. -/
noncomputable def bankDispatchedBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (selectorBits chainBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (branchTargetBitBits (LanguageEvaluationRequest.length request) 0
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))
      (selectorBits request) (chainBits request) 1)
    (branchTargetBitBits (LanguageEvaluationRequest.length request) 1
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))
      (selectorBits request) (chainBits request) 1)

def bankDispatchedBodyFuel (caseOne caseTwo : NPOracleProgram)
    (selectorFuel chainFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  branchTargetBitFuel caseOne caseTwo (selectorFuel request)
    (chainFuel request)

/-! ## 3. `bodyRun`, from the four framed premises -/

set_option maxHeartbeats 1600000 in
-- The two branch envelopes are nested link terms over the whole body.
/-- **The inverse schedule's `bodyRun`.**  The premise
`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` consumes is
discharged for the dispatched body from four premises, each about one named
stage started on the numeral bank's own frame.  Nothing about the request's
target enters the dispatcher. -/
theorem inverse_bodyRun_of_dispatch
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
                  (encodeBitInput input))) =
            some
              (Nat.pair 0
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
                  (encodeBitInput input))))
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
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
                  (encodeBitInput input))) =
            some
              (Nat.pair 1
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent) target
                  (encodeBitInput input))))
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
        runNPOracleProgram (bankDispatchedBodyProgram selector caseOne caseTwo)
            (bankDispatchedBodyBits contracts clockDepth advantageExponent
              selectorBits chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo selectorFuel chainFuel
              ⟨target, input⟩)
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
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input))
          (selectorBits ⟨target, input⟩) (selectorFuel ⟨target, input⟩)
          (chainBits ⟨target, input⟩) (chainFuel ⟨target, input⟩) _
          (hselectorOne target hlarge hyes data hbranch input)
          (hchainOne target hlarge hyes hrejects haccepts data hbranch input)
      exact run_bits_mono hrun
        ((branchTargetBitBits_mono_output _ _ _ _ _ _ houtput).trans
          (Nat.le_max_left _ _))
  | caseTwo branchTwo =>
      have hrun :=
        run_branchTargetBitProgram_caseTwo selector caseOne caseTwo target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input))
          1 (selectorBits ⟨target, input⟩) (selectorFuel ⟨target, input⟩)
          (chainBits ⟨target, input⟩) (chainFuel ⟨target, input⟩) _
          Nat.one_ne_zero
          (hselectorTwo target hlarge hyes branchTwo hbranch input)
          (hchainTwo target hlarge hyes hrejects haccepts branchTwo hbranch
            input)
      exact run_bits_mono hrun
        ((branchTargetBitBits_mono_output _ _ _ _ _ _ houtput).trans
          (Nat.le_max_right _ _))

/-! ## 4. Chaining to `hexecutes`

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` applied to
`bankDispatchedBodyProgram selector caseOne caseTwo`, its width
`bankDispatchedBodyBits`, its fuel `bankDispatchedBodyFuel`, and the `bodyRun`
of §3 discharges the executable target language's terminal obligation for the
linked stream `bank ⊕ dispatcher`; the packaging's own resource premises
(`hbits`, `hfuel`, `hinitial`, `hrun`, `hboolean`) pass through untouched.
-/

end NearCubicWires.BankDispatchedTargetBody

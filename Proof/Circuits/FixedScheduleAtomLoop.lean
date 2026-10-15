import Proof.PCP.PaddedProjectionPresentation

/-!
# The fixed schedule's `bodyRun`, down to the compiler's run

`HeadlineRootSkeleton` §5 stops at a raw `bodyRun` binder because the whole
chain below `UniformTargetLanguageBank.fixed_hexecutes_of_bodyRun` — the
dispatcher, the emitted branch selector, the atom loop and the executable
presentation — was written only at the inverse schedule.  This module is the
fixed-rate twin of that chain.

## The assessment this module implements

Per inverse module of the `bodyRun` chain:

* **GENERIC, serves both schedules as-is.**  Every *program* on the chain, and
  every run lemma stated at an abstract source index.  In particular
  `BankDispatchedTargetBody.bankDispatchedBodyProgram`/`…Fuel`,
  `BankRecoveryCodeProgram.emittedBranchSelectorProgram` with its two closed
  tag lemmas `run_emittedBranchSelectorProgram_caseOne`/`…_caseTwo`,
  `BankEmittedAtomLoop.inverseBankEmitterProgram` (a schedule-free `linkPrograms`
  of an adapter with the atom-emitter loop),
  `StructuralAtomCalleeProgram.run_structuralAtomEmitterProgram_ofCompiler`,
  `PaddedProjectionPresentation.PresentsPaddedOuterPCP` and its four field
  projections, and `PaddedRunnerBudgetClosure.exists_presentsPaddedOuterPCP_published`,
  which mentions no schedule at all and therefore discharges the presentation
  premise of *both* roots.
* **RENAME-REPLAY.**  Everything schedule-indexed on the chain: the resource
  envelopes (`…Bits`/`…Fuel`), the named premise predicates, and the five
  `bodyRun` reductions.  The substitution is
  `advantageExponent : ℝ ↦ requestedRate : ℕ`,
  `inverseSourceIndex (inverseSelectedSource … (inverseCoreAdvantagePower e) t) ↦
   fixedSelectedSource … r t`,
  `inverseRequiredDegree … (inverseCoreAdvantagePower e) ↦ fixedRequiredDegree … r`,
  `inverseRefuterInput ↦ fixedRefuterInput`,
  `inverseCaseOneTargetOnset ↦ fixedCaseOneTargetOnset`,
  `inverseBankRate ↦ fixedBankRate`, `inverseTargetBranch ↦ fixedTargetBranch`,
  `InverseCaseTwoAcceptance ↦ FixedCaseTwoAcceptance`,
  `inverseCanonicalTargetFunction ↦ fixedCanonicalTargetFunction`.
  No proof term changes.
* **GENUINELY DIFFERENT.**  Only one thing, and it makes the fixed side
  *smaller*: the inverse schedule's chain index carries an extra
  `RecoveryScheduleEnvelope.inverseSourceIndex` search in front of the selected
  source, while the fixed chain's index is the selected source itself.  Every
  fixed statement below is therefore one function application shorter than its
  inverse twin.  `CaseOneRecoveryAssembly.fixedCaseOneTargetOnset` is likewise
  one `max` shorter than the inverse onset, because the fixed advantage reserve
  is target independent.

## The diagonal is still needed, and it is already bridged

The fixed schedule is *not* length-uniform: `RuntimeScheduleNumeralBank` decodes
its source index from the request's own public length, whereas the chain works
at `fixedSelectedSource`, and `bodyRun`'s consumer pins neither.  So the fixed
cluster needs a diagonal hypothesis exactly as the inverse cluster does — but
`BankScheduleDiagonal.publishedBankFrame_at_fixedDiagonal` is already green, so
nothing has to be built for it.  What *is* legitimately frozen on this schedule
is the copy register (`RecoveryScheduleEnvelope.fixedCopies`), which is why
`UniformTargetLanguageBank.fixedBankRate` is the bare `fixedRate`.
-/

namespace NearCubicWires.FixedScheduleAtomLoop

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed schedule's PCP request -/

/-- The scheduled source length at one target.  One application shorter than
`BankEmittedAtomLoop.inverseScheduleLength`: no `inverseSourceIndex`. -/
noncomputable def fixedScheduleLength
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate target : ℕ) : ℕ :=
  sourceLength
    (fixedSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)

/-- The scheduled PCP input at one target. -/
noncomputable def fixedScheduleInput
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) :
    BitInput (fixedScheduleLength contracts clockDepth requestedRate target) :=
  fixedRefuterInput contracts (publishedHierarchyOuterPCP contracts clockDepth)
    machine requestedRate target

/-- The scheduled bounded-oracle size bound at one target. -/
noncomputable def fixedScheduleBound
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate target : ℕ) : ℕ :=
  oracleSizeBound (fixedRequiredDegree contracts requestedRate)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (fixedSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target))

theorem fixedSelectorAtoms_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) :
    fixedSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target =
      boundedOracleStructuralFormulaAtoms
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (fixedScheduleInput contracts clockDepth machine requestedRate target)
        (fixedScheduleBound contracts clockDepth requestedRate target) :=
  rfl

/-! ## 2. The loop's generated range at the schedule -/

/-- The number of global formula indices at one target. -/
noncomputable def fixedAtomCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  structuralAtomCount pcp
    (fixedScheduleInput contracts clockDepth machine requestedRate target)
    (fixedScheduleBound contracts clockDepth requestedRate target)

/-- The shared public context of every generated request at one target. -/
noncomputable def fixedAtomContext
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  structuralAtomContext pcp
    (fixedScheduleInput contracts clockDepth machine requestedRate target)
    (fixedScheduleBound contracts clockDepth requestedRate target)

/-! ## 3. The three named hypotheses -/

/-- **The presentation premise at the fixed schedule.** -/
def FixedScheduleAtomsAgree
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : Prop :=
  ∀ target : ℕ,
    boundedOracleStructuralFormulaAtoms pcp.toSemantic
        (fixedScheduleInput contracts clockDepth machine requestedRate target)
        (fixedScheduleBound contracts clockDepth requestedRate target) =
      fixedSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target

/-- **The presentation premise discharges the atom agreement.**  The fixed twin
of `PaddedProjectionPresentation.inverseScheduleAtoms_of_presentation`. -/
theorem fixedScheduleAtoms_of_presentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp) :
    FixedScheduleAtomsAgree contracts clockDepth machine requestedRate pcp := by
  intro target
  rw [hpresentation, boundedOracleStructuralFormulaAtoms_withConstructionSteps,
    fixedSelectorAtoms_eq]

/-- **The frame-lowering premise.**  One stage takes the bank's frame to the
atom loop's input frame and retains the bank's frame as the point code. -/
def FixedFrameAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (input : BitInput target),
    runNPOracleProgram adapter (adapterBits ⟨target, input⟩)
        (adapterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input))) =
      some
        (Nat.pair
          (generatedBalancedRangeInput
            (fixedAtomCount contracts clockDepth machine requestedRate pcp
              target)
            (fixedAtomContext contracts clockDepth machine requestedRate pcp
              target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input)))

def FixedCompilerRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits compilerFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ (target index : ℕ),
    index < fixedAtomCount contracts clockDepth machine requestedRate pcp
      target →
    StructuralCompilerRunsAt pcp
      (fixedScheduleInput contracts clockDepth machine requestedRate target)
      target (fixedScheduleBound contracts clockDepth requestedRate target)
      index (compilerBits target index) (compilerFuel target index)

/-! ## 4. The dispatcher's width at the fixed bank -/

private theorem branchTargetBitBits_mono_output'
    (inputLength tag pointCode selectorBits chainBits output : ℕ)
    (houtput : output ≤ 1) :
    branchTargetBitBits inputLength tag pointCode selectorBits chainBits
        output ≤
      branchTargetBitBits inputLength tag pointCode selectorBits chainBits 1 :=
  max_le_max (Nat.le_refl _)
    (max_le_max (Nat.le_refl _)
      (max_le_max (Nat.le_refl _)
        (max_le_max (Nat.le_refl _) (natBitLength_mono houtput))))

/-- The dispatcher's width at one request on the fixed bank's frame. -/
noncomputable def fixedDispatchedBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (selectorBits chainBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max
    (branchTargetBitBits (LanguageEvaluationRequest.length request) 0
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))
      (selectorBits request) (chainBits request) 1)
    (branchTargetBitBits (LanguageEvaluationRequest.length request) 1
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))
      (selectorBits request) (chainBits request) 1)

/-! ## 5. `bodyRun`, from the four framed premises -/

set_option maxHeartbeats 1600000 in
-- The two branch envelopes are nested link terms over the whole body.
/-- **The fixed schedule's `bodyRun`, from the dispatcher.**  The fixed twin of
`BankDispatchedTargetBody.inverse_bodyRun_of_dispatch`. -/
theorem fixed_bodyRun_of_dispatch
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (selector caseOne caseTwo : NPOracleProgram)
    (selectorBits selectorFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hselectorOne : ∀ target
        (_hlarge :
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
        (data : ScheduledCaseOneData
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedAmplifier contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseOne data →
        ∀ input : BitInput target,
          runNPOracleProgram selector (selectorBits ⟨target, input⟩)
              (selectorFuel ⟨target, input⟩)
              (initialNPOracleState target
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))) =
            some
              (Nat.pair 0
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))))
    (hselectorTwo : ∀ target
        (_hlarge :
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
        (branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseTwo branchTwo →
        ∀ input : BitInput target,
          runNPOracleProgram selector (selectorBits ⟨target, input⟩)
              (selectorFuel ⟨target, input⟩)
              (initialNPOracleState target
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))) =
            some
              (Nat.pair 1
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))))
    (hchainOne : ∀ target
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
          ∀ branchTwo : CanonicalAcceptingOracle
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
              branchTwo machine)
        (data : ScheduledCaseOneData
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedAmplifier contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseOne data →
        ∀ input : BitInput target,
          runNPOracleProgram caseOne (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
              (initialNPOracleState target
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))) =
            some
              (fixedCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                requestedRate target hlarge hyes hrejects haccepts input).toNat)
    (hchainTwo : ∀ target
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
          ∀ branchTwo : CanonicalAcceptingOracle
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
              branchTwo machine)
        (branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseTwo branchTwo →
        ∀ input : BitInput target,
          runNPOracleProgram caseTwo (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
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
        ∀ branchTwo : CanonicalAcceptingOracle
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
            branchTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram (bankDispatchedBodyProgram selector caseOne caseTwo)
            (fixedDispatchedBodyBits contracts clockDepth requestedRate
              selectorBits chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo selectorFuel chainFuel
              ⟨target, input⟩)
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
              input).toNat := by
  intro target hlarge hyes hrejects haccepts input
  have houtput :
      (fixedCanonicalTargetFunction contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target hlarge hyes hrejects haccepts input).toNat ≤
        1 := by
    cases (fixedCanonicalTargetFunction contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target hlarge hyes hrejects haccepts input) <;>
      simp
  cases hbranch :
      fixedTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target hyes with
  | caseOne data =>
      have hrun :=
        run_branchTargetBitProgram_caseOne selector caseOne caseTwo target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input))
          (selectorBits ⟨target, input⟩) (selectorFuel ⟨target, input⟩)
          (chainBits ⟨target, input⟩) (chainFuel ⟨target, input⟩) _
          (hselectorOne target hlarge hyes data hbranch input)
          (hchainOne target hlarge hyes hrejects haccepts data hbranch input)
      exact run_bits_mono hrun
        ((branchTargetBitBits_mono_output' _ _ _ _ _ _ houtput).trans
          (Nat.le_max_left _ _))
  | caseTwo branchTwo =>
      have hrun :=
        run_branchTargetBitProgram_caseTwo selector caseOne caseTwo target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input))
          1 (selectorBits ⟨target, input⟩) (selectorFuel ⟨target, input⟩)
          (chainBits ⟨target, input⟩) (chainFuel ⟨target, input⟩) _
          Nat.one_ne_zero
          (hselectorTwo target hlarge hyes branchTwo hbranch input)
          (hchainTwo target hlarge hyes hrejects haccepts branchTwo hbranch
            input)
      exact run_bits_mono hrun
        ((branchTargetBitBits_mono_output' _ _ _ _ _ _ houtput).trans
          (Nat.le_max_right _ _))

/-! ## 6. The emitter premise at the bank's frame -/

/-- **The one selector-side hypothesis.**  At every onset-large request the
emitter, started on the numeral bank's frame, returns the tagged fixed-schedule
atom stream beside that same frame. -/
def FixedEmitterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (emitter : NPOracleProgram)
    (emitterBits emitterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (input : BitInput target),
    runNPOracleProgram emitter (emitterBits ⟨target, input⟩)
        (emitterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input))) =
      some
        (Nat.pair
          (encodeTaggedList
            (fixedSelectorAtoms contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input)))

/-! ## 7. The selector's resource envelopes at the bank's frame -/

noncomputable def fixedBankSelectorBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (emitterBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  emittedBranchSelectorBits
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      (LanguageEvaluationRequest.length request))
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          (LanguageEvaluationRequest.length request))))
    (LanguageEvaluationRequest.length request)
    (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (fixedBankRate contracts requestedRate)
      (LanguageEvaluationRequest.length request)
      (LanguageEvaluationRequest.code request))
    (emitterBits request)

noncomputable def fixedBankSelectorFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (emitterFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  emittedBranchSelectorFuel
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      (LanguageEvaluationRequest.length request))
    (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          (LanguageEvaluationRequest.length request))))
    (emitterFuel request)

set_option maxHeartbeats 1600000 in
-- The dispatched body's envelopes are nested link terms over the whole stream.
/-- **The fixed schedule's `bodyRun`, selector side closed.**  The fixed twin of
`BankEmittedBranchSelector.inverse_bodyRun_of_emitterRuns`; the two tag lemmas
of `BankRecoveryCodeProgram` are schedule generic and are cited unchanged. -/
theorem fixed_bodyRun_of_emitterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (emitter caseOne caseTwo : NPOracleProgram)
    (emitterBits emitterFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (hemitter :
      FixedEmitterRuns contracts clockDepth machine requestedRate emitter
        emitterBits emitterFuel)
    (hchainOne : ∀ target
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
          ∀ branchTwo : CanonicalAcceptingOracle
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
              branchTwo machine)
        (data : ScheduledCaseOneData
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedAmplifier contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseOne data →
        ∀ input : BitInput target,
          runNPOracleProgram caseOne (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
              (initialNPOracleState target
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))) =
            some
              (fixedCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                requestedRate target hlarge hyes hrejects haccepts input).toNat)
    (hchainTwo : ∀ target
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
          ∀ branchTwo : CanonicalAcceptingOracle
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
              branchTwo machine)
        (branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseTwo branchTwo →
        ∀ input : BitInput target,
          runNPOracleProgram caseTwo (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
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
        ∀ branchTwo : CanonicalAcceptingOracle
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
            branchTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram
            (bankDispatchedBodyProgram (emittedBranchSelectorProgram emitter)
              caseOne caseTwo)
            (fixedDispatchedBodyBits contracts clockDepth requestedRate
              (fixedBankSelectorBits contracts clockDepth machine requestedRate
                emitterBits)
              chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo
              (fixedBankSelectorFuel contracts clockDepth machine requestedRate
                emitterFuel)
              chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (fixedBankRate contracts requestedRate) target
                (encodeBitInput input))) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_bodyRun_of_dispatch contracts clockDepth machine requestedRate
    (emittedBranchSelectorProgram emitter) caseOne caseTwo
    (fixedBankSelectorBits contracts clockDepth machine requestedRate
      emitterBits)
    (fixedBankSelectorFuel contracts clockDepth machine requestedRate
      emitterFuel)
    chainBits chainFuel
    (fun target hlarge _hyes data _hbranch input =>
      run_emittedBranchSelectorProgram_caseOne data target
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (fixedBankRate contracts requestedRate) target
          (encodeBitInput input))
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (fixedBankRate contracts requestedRate) target
          (encodeBitInput input))
        (emitterBits ⟨target, input⟩) (emitterFuel ⟨target, input⟩) emitter
        (hemitter target hlarge input))
    (fun target hlarge _hyes branchTwo _hbranch input =>
      run_emittedBranchSelectorProgram_caseTwo branchTwo target
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (fixedBankRate contracts requestedRate) target
          (encodeBitInput input))
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (fixedBankRate contracts requestedRate) target
          (encodeBitInput input))
        (emitterBits ⟨target, input⟩) (emitterFuel ⟨target, input⟩) emitter
        (hemitter target hlarge input))
    hchainOne hchainTwo

/-! ## 8. The emitter and its resource envelopes

The emitter *program* is schedule free — `BankEmittedAtomLoop.inverseBankEmitterProgram`
is one `linkPrograms` of the given adapter with the fixed atom-emitter loop, and
carries no schedule numeral — so it is reused verbatim under a fixed-side name.
Only its two envelopes are schedule indexed. -/

/-- **The bank-framed emitter**, the schedule-free stream of
`BankEmittedAtomLoop.inverseBankEmitterProgram`. -/
def fixedBankEmitterProgram (adapter : NPOracleProgram) : NPOracleProgram :=
  inverseBankEmitterProgram adapter

noncomputable def fixedBankEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterBits : LanguageEvaluationRequest → ℕ) (rangeBits : ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (adapterBits request)
    (structuralAtomEmitterBits
      (rangeBits (LanguageEvaluationRequest.length request))
      (LanguageEvaluationRequest.length request)
      (fixedAtomCount contracts clockDepth machine requestedRate pcp
        (LanguageEvaluationRequest.length request))
      (fixedAtomContext contracts clockDepth machine requestedRate pcp
        (LanguageEvaluationRequest.length request))
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request))
      (fixedSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        (LanguageEvaluationRequest.length request)))

noncomputable def fixedBankEmitterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterFuel : LanguageEvaluationRequest → ℕ) (compilerFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel (structuralAtomEmitterProgram structuralAtomCalleeProgram)
    (adapterFuel request)
    (structuralAtomEmitterFuel structuralAtomCalleeProgram
      (LanguageEvaluationRequest.length request)
      (fixedAtomCount contracts clockDepth machine requestedRate pcp
        (LanguageEvaluationRequest.length request))
      (fixedAtomContext contracts clockDepth machine requestedRate pcp
        (LanguageEvaluationRequest.length request))
      (structuralAtomCalleeRequestFuel
        (projectionRunnerCallOutputs pcp
          (fixedScheduleInput contracts clockDepth machine requestedRate
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request)))
        (fixedScheduleBound contracts clockDepth requestedRate
          (LanguageEvaluationRequest.length request))
        (compilerFuel (LanguageEvaluationRequest.length request)))
      (fixedSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        (LanguageEvaluationRequest.length request)))

/-! ## 9. The emitter premise, discharged -/

/-- **The selector's emitter premise, from the compiler's run.**  The fixed twin
of `BankEmittedAtomLoop.inverseEmitterRuns_ofCompiler`. -/
theorem fixedEmitterRuns_ofCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hatoms :
      FixedScheduleAtomsAgree contracts clockDepth machine requestedRate pcp)
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hadapter :
      FixedFrameAdapterRuns contracts clockDepth machine requestedRate pcp
        adapter adapterBits adapterFuel)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (fixedAtomCount contracts clockDepth machine requestedRate pcp target)
          (fixedAtomContext contracts clockDepth machine requestedRate pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (fixedAtomContext contracts clockDepth machine requestedRate pcp
                target)
              0
              (fixedAtomCount contracts clockDepth machine requestedRate pcp
                target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (fixedScheduleInput contracts clockDepth machine requestedRate
                target)
              (fixedScheduleBound contracts clockDepth requestedRate target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (fixedAtomContext contracts clockDepth machine requestedRate pcp
              target)
            0
            (fixedAtomCount contracts clockDepth machine requestedRate pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        fixedAtomCount contracts clockDepth machine requestedRate pcp target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target))
          (pcp.nativeWidth
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (pcp.queryCount
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (fixedScheduleBound contracts clockDepth requestedRate target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      FixedCompilerRuns contracts clockDepth machine requestedRate pcp
        compilerBits compilerFuel) :
    FixedEmitterRuns contracts clockDepth machine requestedRate
      (fixedBankEmitterProgram adapter)
      (fixedBankEmitterBits contracts clockDepth machine requestedRate pcp
        adapterBits rangeBits)
      (fixedBankEmitterFuel contracts clockDepth machine requestedRate pcp
        adapterFuel compilerFuel) := by
  intro target hlarge input
  have hloop :=
    run_structuralAtomEmitterProgram_ofCompiler pcp
      (fixedScheduleInput contracts clockDepth machine requestedRate target)
      target (fixedScheduleBound contracts clockDepth requestedRate target)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate) target (encodeBitInput input))
      (compilerBits target) (compilerFuel target) (hpositive target)
      (hlengthBits target) (hrangeBits target) (hlistBits target)
      (hcallBits target) (hcalleeBits target) (hcompiler target)
  rw [hatoms target] at hloop
  exact run_occurrenceStage (hadapter target hlarge input) hloop

/-! ## 10. `bodyRun` from the presentation and the compiler's run -/

set_option maxHeartbeats 1600000 in
-- The dispatched body's envelopes are nested link terms over the whole stream.

theorem fixed_bodyRun_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (adapter caseOne caseTwo : NPOracleProgram)
    (adapterBits adapterFuel chainBits chainFuel :
      LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hadapter :
      FixedFrameAdapterRuns contracts clockDepth machine requestedRate pcp
        adapter adapterBits adapterFuel)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (fixedAtomCount contracts clockDepth machine requestedRate pcp target)
          (fixedAtomContext contracts clockDepth machine requestedRate pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (fixedAtomContext contracts clockDepth machine requestedRate pcp
                target)
              0
              (fixedAtomCount contracts clockDepth machine requestedRate pcp
                target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (fixedScheduleInput contracts clockDepth machine requestedRate
                target)
              (fixedScheduleBound contracts clockDepth requestedRate target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (fixedAtomContext contracts clockDepth machine requestedRate pcp
              target)
            0
            (fixedAtomCount contracts clockDepth machine requestedRate pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        fixedAtomCount contracts clockDepth machine requestedRate pcp target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target))
          (pcp.nativeWidth
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (pcp.queryCount
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (fixedScheduleBound contracts clockDepth requestedRate target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      FixedCompilerRuns contracts clockDepth machine requestedRate pcp
        compilerBits compilerFuel)
    (hchainOne : ∀ target
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
          ∀ branchTwo : CanonicalAcceptingOracle
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
              branchTwo machine)
        (data : ScheduledCaseOneData
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedAmplifier contracts)
          (fixedRequiredDegree contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseOne data →
        ∀ input : BitInput target,
          runNPOracleProgram caseOne (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
              (initialNPOracleState target
                (publishedBankFrame
                  (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (fixedBankRate contracts requestedRate) target
                  (encodeBitInput input))) =
            some
              (fixedCanonicalTargetFunction contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                requestedRate target hlarge hyes hrejects haccepts input).toNat)
    (hchainTwo : ∀ target
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
          ∀ branchTwo : CanonicalAcceptingOracle
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
              branchTwo machine)
        (branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target)),
        fixedTargetBranch contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hyes = .caseTwo branchTwo →
        ∀ input : BitInput target,
          runNPOracleProgram caseTwo (chainBits ⟨target, input⟩)
              (chainFuel ⟨target, input⟩)
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
        ∀ branchTwo : CanonicalAcceptingOracle
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
            branchTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram
            (bankDispatchedBodyProgram
              (emittedBranchSelectorProgram (fixedBankEmitterProgram adapter))
              caseOne caseTwo)
            (fixedDispatchedBodyBits contracts clockDepth requestedRate
              (fixedBankSelectorBits contracts clockDepth machine requestedRate
                (fixedBankEmitterBits contracts clockDepth machine requestedRate
                  pcp adapterBits rangeBits))
              chainBits ⟨target, input⟩)
            (bankDispatchedBodyFuel caseOne caseTwo
              (fixedBankSelectorFuel contracts clockDepth machine requestedRate
                (fixedBankEmitterFuel contracts clockDepth machine requestedRate
                  pcp adapterFuel compilerFuel))
              chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (fixedBankRate contracts requestedRate) target
                (encodeBitInput input))) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_bodyRun_of_emitterRuns contracts clockDepth machine requestedRate
    (fixedBankEmitterProgram adapter) caseOne caseTwo
    (fixedBankEmitterBits contracts clockDepth machine requestedRate pcp
      adapterBits rangeBits)
    (fixedBankEmitterFuel contracts clockDepth machine requestedRate pcp
      adapterFuel compilerFuel)
    chainBits chainFuel
    (fixedEmitterRuns_ofCompiler contracts clockDepth machine requestedRate pcp
      (fixedScheduleAtoms_of_presentation contracts clockDepth machine
        requestedRate pcp hpresentation)
      adapter adapterBits adapterFuel rangeBits compilerBits compilerFuel
      hadapter hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits
      hcompiler)
    hchainOne hchainTwo

end NearCubicWires.FixedScheduleAtomLoop

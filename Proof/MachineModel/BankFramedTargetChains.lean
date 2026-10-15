import Proof.MachineModel.BankFrameLoweringAdapter
import Proof.PCP.PaddedProjectionPresentation

/-!
# The two target chains at the numeral bank's frame

`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` consumes its two
chain premises `hchainOne`/`hchainTwo` at the numeral bank's own frame

`publishedBankFrame outer pcppSource rate target (encodeBitInput input)`,

whereas every closed chain run in the tree
(`BranchTargetLanguageProgram.run_inverseCaseOneChainProgram`,
`CaseTwoBlockOccurrenceProgram.run_caseTwoTargetBitFromPointRangeProgram_inverse_closed`)
is stated at the bare requested point code `encodeBitInput input`.  This module
removes that gap once and for all.

## The frame half is unconditional

`RuntimeScheduleNumeralBank.scheduleNumeralBankOutput` puts the retained point
code in the innermost right position of a four-register pairing, and
`publishedBankFrame` is that word at the length-decoded registers.  Recovering
the point code is therefore four right projections — no schedule numeral is
read, no source index is decoded, and **no diagonal identification is needed**:
the projection is correct at every public length, on or off the schedule's
diagonal.  §2 executes it and §3 wraps an arbitrary chain behind it.

This is the one reusable call frame of the bank-framed body: any stage already
verified from the requested point code is re-framed to the bank's frame by
`run_bankFramedChainProgram_published`, at one extra link and five instructions,
with no hypothesis about the stage beyond its own run.

## What is left after it

§4 names the two residual premises in their point-code form
(`InverseCaseOnePointRuns`, `InverseCaseTwoPointRuns`) and §5 discharges
`hchainOne` and `hchainTwo` from them.  Both residuals are *frame free*: they
say nothing about the bank, the registers, or the diagonal.  What they still
demand — and what this module deliberately does not hide — is that the chain be
**one fixed instruction stream for every target**, whereas
`inverseCaseOneChainProgram` and the Case-2 occurrence callee are still indexed
by the request's own target through their scheduled immediates.  That residue is
a property of those chains, not of the frame, and it is now the only thing
between the closed chain runs and `bodyRun`.
-/

namespace NearCubicWires.BankFramedTargetChains

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Bookkeeping -/

private theorem run_fuel_mono {program : NPOracleProgram}
    {maximumBits fuel target : ℕ} {state : NPOracleState} {output : ℕ}
    (hexec : runNPOracleProgram program maximumBits fuel state = some output)
    (hfuel : fuel ≤ target) :
    runNPOracleProgram program maximumBits target state = some output := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  exact run_fuel_add hexec extra

private theorem natBitLength_mono' {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

private theorem right_bits_le (left right : ℕ) :
    natBitLength right ≤ natBitLength (Nat.pair left right) :=
  natBitLength_mono' (Nat.right_le_pair left right)

/-! ## 2. The bank frame's point-code projection -/

/-- Four right projections: the retained point code out of the numeral bank's
four-register frame.  Nothing else in the frame is read. -/
private def bankCodeProjectProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .unpairRight 0 0 2
  , .unpairRight 0 0 3
  , .unpairRight 0 0 4
  , .halt 0
  ]

@[simp] private theorem bankCodeProjectProgram_oracleFree :
    OracleFree bankCodeProjectProgram := by
  rfl

/-- Width of the projection: the frame itself dominates every intermediate. -/
private def bankCodeProjectBits
    (sourceLen width queryCount copies code : ℕ) : ℕ :=
  natBitLength
    (scheduleNumeralBankOutput sourceLen width queryCount copies code)

private theorem run_bankCodeProjectProgram
    (inputLength sourceLen width queryCount copies code : ℕ) :
    runNPOracleProgram bankCodeProjectProgram
        (bankCodeProjectBits sourceLen width queryCount copies code) 5
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            code)) =
      some code := by
  have hbitsOne :
      natBitLength (Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
        ≤ bankCodeProjectBits sourceLen width queryCount copies code :=
    right_bits_le _ _
  have hbitsTwo :
      natBitLength (Nat.pair queryCount (Nat.pair copies code)) ≤
        bankCodeProjectBits sourceLen width queryCount copies code :=
    (right_bits_le _ _).trans hbitsOne
  have hbitsThree :
      natBitLength (Nat.pair copies code) ≤
        bankCodeProjectBits sourceLen width queryCount copies code :=
    (right_bits_le _ _).trans hbitsTwo
  have hbitsFour :
      natBitLength code ≤
        bankCodeProjectBits sourceLen width queryCount copies code :=
    (right_bits_le _ _).trans hbitsThree
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair queryCount (Nat.pair copies code)))
    (by rfl) rfl (by simp [initialNPOracleState, scheduleNumeralBankOutput])
    hbitsOne]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair queryCount (Nat.pair copies code))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hbitsTwo]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair copies code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hbitsThree]
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hbitsFour]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbitsFour

/-! ## 3. The re-framing wrapper -/

/-- **The bank-framed call frame.**  One projection stage in front of a chain
already verified from the requested point code. -/
def bankFramedChainProgram (chain : NPOracleProgram) : NPOracleProgram :=
  linkPrograms bankCodeProjectProgram chain

theorem bankFramedChainProgram_oracleFree {chain : NPOracleProgram}
    (hchain : OracleFree chain) :
    OracleFree (bankFramedChainProgram chain) :=
  oracleFree_linkPrograms bankCodeProjectProgram_oracleFree hchain

/-- **The re-framing lemma.**  A stage verified from the point code runs
unchanged from the numeral bank's frame.  No schedule numeral is used, so the
statement holds at every public length. -/
theorem run_bankFramedChainProgram {chain : NPOracleProgram}
    {inputLength sourceLen width queryCount copies code chainBits chainFuel
      fuel output : ℕ}
    (hchain :
      runNPOracleProgram chain chainBits chainFuel
        (initialNPOracleState inputLength code) = some output)
    (hfuel : linkFuel chain 5 chainFuel ≤ fuel) :
    runNPOracleProgram (bankFramedChainProgram chain)
        (occurrenceStageBits inputLength
          (bankCodeProjectBits sourceLen width queryCount copies code)
          chainBits)
        fuel
        (initialNPOracleState inputLength
          (scheduleNumeralBankOutput sourceLen width queryCount copies
            code)) =
      some output :=
  run_fuel_mono
    (run_occurrenceStage
      (run_bankCodeProjectProgram inputLength sourceLen width queryCount copies
        code)
      hchain)
    hfuel

/-- The width the wrapper is charged at one request. -/
noncomputable def bankFramedChainBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (chainBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (natBitLength
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request)))
    (chainBits request)

/-- The fuel the wrapper is charged at one request.  The dispatcher shares one
fuel function between the two chains, so the envelope covers both links. -/
def bankFramedChainFuel (caseOne caseTwo : NPOracleProgram)
    (chainFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  max (linkFuel caseOne 5 (chainFuel request))
    (linkFuel caseTwo 5 (chainFuel request))

/-- **The re-framing lemma at the published inverse bank.** -/
theorem run_bankFramedChainProgram_published {chain : NPOracleProgram}
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) {target : ℕ} (input : BitInput target)
    {chainBits chainFuel fuel output : ℕ}
    (hchain :
      runNPOracleProgram chain chainBits chainFuel
        (initialNPOracleState target (encodeBitInput input)) = some output)
    (hfuel : linkFuel chain 5 chainFuel ≤ fuel) :
    runNPOracleProgram (bankFramedChainProgram chain)
        (bankFramedChainBits contracts clockDepth advantageExponent
          (fun _ => chainBits) ⟨target, input⟩)
        fuel
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (encodeBitInput input))) =
      some output :=
  run_bankFramedChainProgram hchain hfuel

/-! ## 4. The two chain premises, frame free -/

/-- **The Case-1 chain at the requested point code.**  The premise
`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` carries as
`hchainOne`, with the numeral bank removed from it. -/
def InverseCaseOnePointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (caseOne : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ) : Prop :=
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
          (initialNPOracleState target (encodeBitInput input)) =
        some
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts input).toNat

/-- **The Case-2 chain at the requested point code.** -/
def InverseCaseTwoPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ) : Prop :=
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
          (initialNPOracleState target (encodeBitInput input)) =
        some
          (inverseCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            advantageExponent target hlarge hyes hrejects haccepts input).toNat

/-! ## 5. The dispatcher's chain premises, discharged -/

/-- **`hchainOne` from the point-code chain.**  Exactly the premise
`inverse_bodyRun_ofPresentation` consumes, for the re-framed Case-1 chain. -/
theorem inverse_chainOne_ofPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (hone :
      InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
        caseOne chainBits chainFuel) :
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
        runNPOracleProgram (bankFramedChainProgram caseOne)
            (bankFramedChainBits contracts clockDepth advantageExponent
              chainBits ⟨target, input⟩)
            (bankFramedChainFuel caseOne caseTwo chainFuel ⟨target, input⟩)
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
  intro target hlarge hyes hrejects haccepts data hbranch input
  exact run_bankFramedChainProgram_published contracts clockDepth
    advantageExponent input
    (hone target hlarge hyes hrejects haccepts data hbranch input)
    (Nat.le_max_left _ _)

/-- **`hchainTwo` from the point-code chain.** -/
theorem inverse_chainTwo_ofPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (htwo :
      InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
        caseTwo chainBits chainFuel) :
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
        runNPOracleProgram (bankFramedChainProgram caseTwo)
            (bankFramedChainBits contracts clockDepth advantageExponent
              chainBits ⟨target, input⟩)
            (bankFramedChainFuel caseOne caseTwo chainFuel ⟨target, input⟩)
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
  intro target hlarge hyes hrejects haccepts branchTwo hbranch input
  exact run_bankFramedChainProgram_published contracts clockDepth
    advantageExponent input
    (htwo target hlarge hyes hrejects haccepts branchTwo hbranch input)
    (Nat.le_max_right _ _)

end NearCubicWires.BankFramedTargetChains

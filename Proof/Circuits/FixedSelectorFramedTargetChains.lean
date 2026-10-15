import Proof.MachineModel.BankFramedTargetChains
import Proof.PCP.FixedSelectorProjectionTableStage

/-!
# Fixed target chains at the selector-driven frame

The bank-framed chain wrapper immediately projects four right components and
runs its chain from the retained request code.  This module specializes that
single frame-independent trace to `fixedSelectorAdapterFrame`; the Case-1
and Case-2 semantics remain the existing point-code runs.
-/

namespace NearCubicWires.FixedSelectorFramedTargetChains

open NearCubicWires
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.FixedSelectorProjectionTableStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.FixedSelectorAtomContextReplay
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private bankCodeProjectBits from Proof.MachineModel.BankFramedTargetChains

/-- Width of the four-right-projection wrapper at an explicitly supplied
frame. -/
noncomputable def selectorBankFramedChainBits
    (pointCode : LanguageEvaluationRequest → ℕ)
    (chainBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (natBitLength (pointCode request)) (chainBits request)

/-- The fixed selector bank's five registers, stated before packaging them as a
language request.  Keeping this join `rfl` avoids unfolding the dependent
request wrapper during the framed-chain trace. -/
private theorem fixedSelectorBankFrame_eq_raw
    (contracts : PublishedContracts) (clockDepth requestedRate target code : ℕ) :
    selectorDrivenBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate)
        (fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)
        code =
      scheduleNumeralBankOutput
        (fixedScheduleLength contracts clockDepth requestedRate target)
        (fixedSelectorBankWidth contracts clockDepth requestedRate target)
        (fixedSelectorBankQueryCount contracts clockDepth requestedRate target)
        (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (fixedBankRate contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        code :=
  rfl

set_option maxHeartbeats 1600000 in
-- The concrete selector frame contains the noncomputable scheduled index.
/-- The generic bank-frame projection run, specialized to the selector bank. -/
theorem run_bankFramedChainProgram_atFixedSelectorFrame {chain : NPOracleProgram}
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (requestedRate : ℕ) {target : ℕ} (input : BitInput target)
    {chainBits chainFuel fuel output : ℕ}
    (hchain :
      runNPOracleProgram chain chainBits chainFuel
        (initialNPOracleState target (encodeBitInput input)) = some output)
    (hfuel : linkFuel chain 5 chainFuel ≤ fuel) :
    runNPOracleProgram (bankFramedChainProgram chain)
        (selectorBankFramedChainBits
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate)
          (fun _ => chainBits) ⟨target, input⟩)
        fuel
        (initialNPOracleState target
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some output := by
  unfold fixedSelectorAdapterFrame
  rw [fixedSelectorBankFrame_eq_raw]
  simpa only [selectorBankFramedChainBits, bankCodeProjectBits,
    LanguageEvaluationRequest.length, LanguageEvaluationRequest.code,
    fixedSelectorBankFrame_eq_raw] using
    (run_bankFramedChainProgram
      (chain := chain) (inputLength := target)
      (sourceLen := fixedScheduleLength contracts clockDepth requestedRate
        target)
      (width := fixedSelectorBankWidth contracts clockDepth requestedRate
        target)
      (queryCount := fixedSelectorBankQueryCount contracts clockDepth
        requestedRate target)
      (copies := inverseCopies
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate)
        (fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          target))
      (code := encodeBitInput input) (chainBits := chainBits)
      (chainFuel := chainFuel) (fuel := fuel) (output := output) hchain hfuel)

/-! ## The two selector-frame chain premises -/

theorem fixed_selectorChainOne_ofPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (hone :
      FixedCaseOnePointRuns contracts clockDepth machine requestedRate
        caseOne chainBits chainFuel) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          requestedRate ≤ target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength (id
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (id requestedRate) target)))
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
            (fixedRequiredDegree contracts
              (id requestedRate)))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (id requestedRate)
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (id requestedRate) target)
            branchTwo machine)
      (data : ScheduledCaseOneData
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedAmplifier contracts)
        (fixedRequiredDegree contracts
          (id requestedRate))
        (id
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (id requestedRate) target))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target)),
      fixedTargetBranch contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target hyes = .caseOne data →
      ∀ input : BitInput target,
        runNPOracleProgram (bankFramedChainProgram caseOne)
            (selectorBankFramedChainBits
              (fixedSelectorAdapterFrame contracts clockDepth requestedRate)
              chainBits ⟨target, input⟩)
            (bankFramedChainFuel caseOne caseTwo chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (fixedSelectorAdapterFrame contracts clockDepth requestedRate
                ⟨target, input⟩)) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts
              input).toNat := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  exact run_bankFramedChainProgram_atFixedSelectorFrame contracts clockDepth
    requestedRate input
    (hone target hlarge hyes hrejects haccepts data hbranch input)
    (Nat.le_max_left _ _)

/-- **`hchainTwo` from the point-code chain.** -/
theorem fixed_selectorChainTwo_ofPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (htwo :
      FixedCaseTwoPointRuns contracts clockDepth machine requestedRate
        caseTwo chainBits chainFuel) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          requestedRate ≤ target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength (id
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (id requestedRate) target)))
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
            (fixedRequiredDegree contracts
              (id requestedRate)))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (id requestedRate)
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (id requestedRate) target)
            branchTwo machine)
      (branchTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts
            (id requestedRate)))
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target)),
      fixedTargetBranch contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target hyes = .caseTwo branchTwo →
      ∀ input : BitInput target,
        runNPOracleProgram (bankFramedChainProgram caseTwo)
            (selectorBankFramedChainBits
              (fixedSelectorAdapterFrame contracts clockDepth requestedRate)
              chainBits ⟨target, input⟩)
            (bankFramedChainFuel caseOne caseTwo chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (fixedSelectorAdapterFrame contracts clockDepth requestedRate
                ⟨target, input⟩)) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts
              input).toNat := by
  intro target hlarge hyes hrejects haccepts branchTwo hbranch input
  exact run_bankFramedChainProgram_atFixedSelectorFrame contracts clockDepth
    requestedRate input
    (htwo target hlarge hyes hrejects haccepts branchTwo hbranch input)
    (Nat.le_max_right _ _)

end NearCubicWires.FixedSelectorFramedTargetChains

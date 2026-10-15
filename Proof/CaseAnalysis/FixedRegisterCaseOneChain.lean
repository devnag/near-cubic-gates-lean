import Proof.MachineModel.BankRegisterCaseOneChain
import Proof.Circuits.FixedScheduleDiagonalClosure

/-!
# The fixed schedule's Case-1 chain, with every numeral read from a register

The fixed twin of `BankRegisterCaseOneChain`.  Nothing below the schedule is
replayed: §1 of that module — `bankRegisterCaseOneTargetBitProgram` and
`run_bankRegisterCaseOneTargetBitProgram`, the refuter-word frame for the
scheduled source length and the formula seed for the scheduled width — is
schedule free and is cited unchanged.  What this module supplies is the two
schedule-specific halves the inverse module states for its own schedule:

* §1 the chain at the requested point code, with the published numeral bank in
  front, at the **fixed** bank rate;
* §2 `FixedScheduleDiagonalClosure.FixedCaseOnePointRuns` from one residual,
  the decision-row stage — the exact twin of
  `BankRegisterCaseOneChain.inverseCaseOnePointRuns_ofRow`.

The fixed chain's index is `CaseOneRecoveryAssembly.fixedSelectedSource`
itself, with no `RecoveryScheduleEnvelope.inverseSourceIndex` in front of it, so
every statement below is one function application shorter than the inverse one.

`hdiagonal` is threaded, never asserted: this module says what the chain does
*given* that the requested public length is the scheduled source length, and
says nothing about whether any target satisfies that.
-/

namespace NearCubicWires.FixedRegisterCaseOneChain

open NearCubicWires
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankOuterProofFormulaSeedProgram
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The chain from the requested point code -/

/-- The fixed schedule's own source index at one target. -/
noncomputable def fixedChainSourceIndex (contracts : PublishedContracts)
    (clockDepth : ℕ) (requestedRate target : ℕ) : ℕ :=
  fixedSelectedSource contracts
    (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target

/-- The published amplifier's request at one target. -/
noncomputable def fixedChainAmplifierRequest (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate target : ℕ) : AmplifierRequest :=
  scheduledAmplifierRequest (publishedHierarchyOuterPCP contracts clockDepth)
    (fixedChainSourceIndex contracts clockDepth requestedRate target)
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)

/-- **The register-driven Case-1 chain at the requested point code.**  The
published numeral bank at the fixed rate, then §1 of `BankRegisterCaseOneChain`. -/
noncomputable def fixedChainOneProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ) (row : NPOracleProgram) : NPOracleProgram :=
  uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts) (fixedBankRate contracts requestedRate)
    (bankRegisterCaseOneTargetBitProgram (publishedAmplifier contracts).algorithm
      (publishedRefuterSource contracts clockDepth).refuter.runner.program row
      machine.description clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent)

/-- Width of the bank-framed body at one request. -/
noncomputable def fixedChainOneBodyBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ) (rowBits : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  bankRegisterCaseOneTargetBitBits (publishedAmplifier contracts).algorithm
    (publishedHierarchyOuterPCP contracts clockDepth) machine
    (fixedChainSourceIndex contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.length request)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (fixedChainSourceIndex contracts clockDepth requestedRate
        (LanguageEvaluationRequest.length request)))
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
      (sourceLength
        (fixedChainSourceIndex contracts clockDepth requestedRate
          (LanguageEvaluationRequest.length request))))
    (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts) (fixedBankRate contracts requestedRate)
      (fixedChainSourceIndex contracts clockDepth requestedRate
        (LanguageEvaluationRequest.length request)))
    (LanguageEvaluationRequest.code request)
    (targetBitCaseOneBits (publishedAmplifier contracts).algorithm
      (LanguageEvaluationRequest.length request)
      ((publishedAmplifier contracts).algorithm.outputArity
        (fixedChainAmplifierRequest contracts clockDepth machine requestedRate
          (LanguageEvaluationRequest.length request)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (fixedChainAmplifierRequest contracts clockDepth machine requestedRate
          (LanguageEvaluationRequest.length request)))
      (LanguageEvaluationRequest.code request))
    (rowBits (LanguageEvaluationRequest.length request))

/-- Fuel of the bank-framed body at one request. -/
noncomputable def fixedChainOneBodyFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ) (row : NPOracleProgram) (rowFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  bankRegisterCaseOneTargetBitFuel (publishedAmplifier contracts).algorithm row
    (publishedHierarchyOuterPCP contracts clockDepth) machine
    (fixedChainSourceIndex contracts clockDepth requestedRate
      (LanguageEvaluationRequest.length request))
    (rowFuel (LanguageEvaluationRequest.length request))
    (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
      ((publishedAmplifier contracts).algorithm.outputArity
        (fixedChainAmplifierRequest contracts clockDepth machine requestedRate
          (LanguageEvaluationRequest.length request)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (fixedChainAmplifierRequest contracts clockDepth machine requestedRate
          (LanguageEvaluationRequest.length request)))
      (LanguageEvaluationRequest.code request))

/-- Width of the whole chain at one request. -/
noncomputable def fixedChainOneBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ) (rowBits : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts) (fixedBankRate contracts requestedRate)
    (fixedChainOneBodyBits contracts clockDepth machine requestedRate rowBits)
    request

/-- Fuel of the whole chain at one request. -/
noncomputable def fixedChainOneFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ) (row : NPOracleProgram) (rowFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts) (fixedBankRate contracts requestedRate)
    (bankRegisterCaseOneTargetBitProgram (publishedAmplifier contracts).algorithm
      (publishedRefuterSource contracts clockDepth).refuter.runner.program row
      machine.description clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent)
    (fixedChainOneBodyFuel contracts clockDepth machine requestedRate row rowFuel)
    request

/-! ## 2. `FixedCaseOnePointRuns`, from the row stage alone -/

/-- **The fixed Case-1 chain's one residual.**  One decision-row stage emitting,
at the fixed schedule's own index and public length, the padded decision row of
every requested randomness code below the scheduled width. -/
def FixedScheduledRowRuns (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (row : NPOracleProgram) (rowBits rowFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤ target)
    (code : ℕ),
    code <
      2 ^ scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (fixedChainSourceIndex contracts clockDepth requestedRate target) →
    runNPOracleProgram row (rowBits target code) (rowFuel target code)
        (initialNPOracleState
          (sourceLength
            (fixedChainSourceIndex contracts clockDepth requestedRate target))
          (Nat.pair code
            (Nat.pair
              (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
                (fixedChainSourceIndex contracts clockDepth requestedRate
                  target))
              (encodeBitInput
                (fixedRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  requestedRate target))))) =
      some
        (encodeTaggedList
          (outerProofRowStream
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (fixedRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target) code))

/-- **`FixedCaseOnePointRuns` from the row stage alone.**  Every other scheduled
numeral of the fixed Case-1 chain is a register read: the source length by
`BankRefuterWordFrameProgram`, the width by `BankOuterProofFormulaSeedProgram`,
and the bank itself by `UniformTargetLanguageBank`. -/
theorem fixedCaseOnePointRuns_ofRow (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (requestedRate : ℕ) (row : NPOracleProgram) (rowBits rowFuel : ℕ → ℕ → ℕ)
    (hrow :
      FixedScheduledRowRuns contracts clockDepth machine requestedRate row
        rowBits rowFuel)
    (hdiagonal : ∀ target : ℕ,
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target →
      target =
        sourceLength
          (fixedChainSourceIndex contracts clockDepth requestedRate target)) :
    FixedCaseOnePointRuns contracts clockDepth machine requestedRate
      (fixedChainOneProgram contracts clockDepth machine requestedRate row)
      (fixedChainOneBits contracts clockDepth machine requestedRate rowBits)
      (fixedChainOneFuel contracts clockDepth machine requestedRate row
        rowFuel) := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  rw [fixedCanonicalTargetFunction_caseOne_apply contracts
    (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
    target hlarge hyes hrejects haccepts data hbranch input]
  refine run_uniformTargetProgram (publishedHierarchyOuterPCP contracts
    clockDepth) (publishedPointwisePCPP contracts)
    (fixedBankRate contracts requestedRate) _ _ _ target input _ ?_
  rw [publishedBankFrame_at_fixedDiagonal contracts clockDepth requestedRate
    target (encodeBitInput input) (hdiagonal target hlarge)]
  exact run_bankRegisterCaseOneTargetBitProgram
    (publishedAmplifier contracts).algorithm row
    (publishedHierarchyOuterPCP contracts clockDepth) machine
    (fixedChainSourceIndex contracts clockDepth requestedRate target)
    target _ _ _ (encodeBitInput input) _ _ _ (rowBits target) (rowFuel target)
    (hrow target hlarge)
    (run_targetBitProgram_fixedCaseOne contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target
      (fixedCaseOneTargetOnset_ready contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target
        hlarge).1
      data hyes
      (fixedCaseOneTargetOnset_ready contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target
        hlarge).2
      input)

end NearCubicWires.FixedRegisterCaseOneChain

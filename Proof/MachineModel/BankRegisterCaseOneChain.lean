import Proof.MachineModel.BankFramedTargetChains
import Proof.MachineModel.BankOuterProofFormulaSeedProgram
import Proof.MachineModel.BranchTargetLanguageProgram

namespace NearCubicWires.BankRegisterCaseOneChain

open NearCubicWires
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankOuterProofFormulaSeedProgram
open NearCubicWires.BankRefuterWordFrameProgram
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

/-! ## 1. The Case-1 chain from the numeral bank's frame -/

/-- **The register-driven Case-1 chain.**  The refuter-word frame reads the
scheduled source length from a register and the recovery seed recomputes the
scheduled width from its own length register, so the only parameters left are
the named decision row stage and the frozen published numerals. -/
def bankRegisterCaseOneTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (refuterProgram row : NPOracleProgram)
    (description clockDepth coefficient exponent : ℕ) : NPOracleProgram :=
  linkPrograms (bankRefuterWordFrameProgram refuterProgram description)
    (caseOneTargetBitProgram algorithm
      (bankOuterProofFormulaSeedProgram row clockDepth coefficient exponent))

noncomputable def bankRegisterCaseOneTargetBitBits
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target width queryCount copies pointCode targetBits : ℕ)
    (rowBits : ℕ → ℕ) : ℕ :=
  occurrenceStageBits target
    (bankRefuterWordFrameBits source.refuter machine target
      (sourceLength sourceIndex) width queryCount copies pointCode)
    (caseOneTargetBitBits algorithm outer sourceIndex
      (scheduledRefuterWord source machine sourceIndex)
      (bankOuterProofFormulaSeedBits clockDepth outer.pcp.shape.coefficient
        outer.proofExponent (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowBits)
      target pointCode targetBits)

noncomputable def bankRegisterCaseOneTargetBitFuel
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) (row : NPOracleProgram)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex : ℕ) (rowFuel : ℕ → ℕ) (targetFuel : ℕ) : ℕ :=
  linkFuel
    (caseOneTargetBitProgram algorithm
      (bankOuterProofFormulaSeedProgram row clockDepth
        outer.pcp.shape.coefficient outer.proofExponent))
    (bankRefuterWordFrameFuel source.refuter machine (sourceLength sourceIndex))
    (caseOneTargetBitFuel algorithm
      (bankOuterProofFormulaSeedProgram row clockDepth
        outer.pcp.shape.coefficient outer.proofExponent)
      outer sourceIndex (scheduledRefuterWord source machine sourceIndex)
      (bankOuterProofFormulaSeedFuel row clockDepth
        outer.pcp.shape.coefficient outer.proofExponent (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowFuel)
      targetFuel)

/-- **The register-driven Case-1 chain, executed from the bank's frame.**  Both
scheduled numerals of `run_bankCaseOneTargetBitProgram` are gone: the source
length is a register read and the width is recomputed by the seed. -/
theorem run_bankRegisterCaseOneTargetBitProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (row : NPOracleProgram) {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (sourceIndex target width queryCount copies pointCode targetBits targetFuel
      value : ℕ)
    (rowBits rowFuel : ℕ → ℕ)
    (hrow : ∀ code, code < 2 ^ scheduledWidth outer sourceIndex →
      runNPOracleProgram row (rowBits code) (rowFuel code)
          (initialNPOracleState (sourceLength sourceIndex)
            (Nat.pair code
              (Nat.pair (scheduledWidth outer sourceIndex)
                (encodeBitInput
                  (scheduledRefuterWord source machine sourceIndex))))) =
        some
          (encodeTaggedList
            (outerProofRowStream (paddedOuterPCP outer)
              (scheduledRefuterWord source machine sourceIndex) code)))
    (htarget :
      runNPOracleProgram (targetBitProgram algorithm) targetBits targetFuel
          (initialNPOracleState target
            (targetBitCaseOneInput
              (algorithm.outputArity
                (scheduledAmplifierRequest outer sourceIndex
                  (scheduledRefuterWord source machine sourceIndex)))
              (algorithm.descriptor
                (scheduledAmplifierRequest outer sourceIndex
                  (scheduledRefuterWord source machine sourceIndex)))
              pointCode)) =
        some value) :
    runNPOracleProgram
        (bankRegisterCaseOneTargetBitProgram algorithm
          source.refuter.runner.program row machine.description clockDepth
          outer.pcp.shape.coefficient outer.proofExponent)
        (bankRegisterCaseOneTargetBitBits algorithm outer machine sourceIndex
          target width queryCount copies pointCode targetBits rowBits)
        (bankRegisterCaseOneTargetBitFuel algorithm row outer machine
          sourceIndex rowFuel targetFuel)
        (initialNPOracleState target
          (scheduleNumeralBankOutput (sourceLength sourceIndex) width queryCount
            copies pointCode)) =
      some value :=
  run_occurrenceStage
    (run_bankRefuterWordFrameProgram source.refuter machine target
      (sourceLength sourceIndex) width queryCount copies pointCode)
    (run_caseOneTargetBitProgram algorithm
      (bankOuterProofFormulaSeedProgram row clockDepth
        outer.pcp.shape.coefficient outer.proofExponent)
      outer sourceIndex (scheduledRefuterWord source machine sourceIndex)
      (bankOuterProofFormulaSeedBits clockDepth outer.pcp.shape.coefficient
        outer.proofExponent (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowBits)
      (bankOuterProofFormulaSeedFuel row clockDepth
        outer.pcp.shape.coefficient outer.proofExponent (paddedOuterPCP outer)
        (scheduledRefuterWord source machine sourceIndex) rowFuel)
      target pointCode targetBits targetFuel value
      (run_bankOuterProofRecoveryFormulaSeedProgram row outer sourceIndex
        (scheduledRefuterWord source machine sourceIndex) rowBits rowFuel hrow)
      htarget)

/-! ## 2. The chain from the requested point code -/

/-- The schedule's own source index at one target. -/
noncomputable def inverseChainSourceIndex
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  inverseSourceIndex
    (inverseSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseCoreAdvantagePower advantageExponent) target)

/-- The published amplifier's request at one target. -/
noncomputable def inverseChainAmplifierRequest
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target : ℕ) : AmplifierRequest :=
  scheduledAmplifierRequest (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseChainSourceIndex contracts clockDepth advantageExponent target)
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)

/-- **The register-driven Case-1 chain at the requested point code.**  The
published numeral bank, then the chain of §1. -/
noncomputable def inverseChainOneProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row : NPOracleProgram) : NPOracleProgram :=
  uniformTargetProgram (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (bankRegisterCaseOneTargetBitProgram (publishedAmplifier contracts).algorithm
      (publishedRefuterSource contracts clockDepth).refuter.runner.program row
      machine.description clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent)

/-- Width of the bank-framed body at one request. -/
noncomputable def inverseChainOneBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (rowBits : ℕ → ℕ → ℕ) (request : LanguageEvaluationRequest) : ℕ :=
  bankRegisterCaseOneTargetBitBits (publishedAmplifier contracts).algorithm
    (publishedHierarchyOuterPCP contracts clockDepth) machine
    (inverseChainSourceIndex contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.length request)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseChainSourceIndex contracts clockDepth advantageExponent
        (LanguageEvaluationRequest.length request)))
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
      (sourceLength
        (inverseChainSourceIndex contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request))))
    (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseChainSourceIndex contracts clockDepth advantageExponent
        (LanguageEvaluationRequest.length request)))
    (LanguageEvaluationRequest.code request)
    (targetBitCaseOneBits (publishedAmplifier contracts).algorithm
      (LanguageEvaluationRequest.length request)
      ((publishedAmplifier contracts).algorithm.outputArity
        (inverseChainAmplifierRequest contracts clockDepth machine
          advantageExponent (LanguageEvaluationRequest.length request)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (inverseChainAmplifierRequest contracts clockDepth machine
          advantageExponent (LanguageEvaluationRequest.length request)))
      (LanguageEvaluationRequest.code request))
    (rowBits (LanguageEvaluationRequest.length request))

/-- Fuel of the bank-framed body at one request. -/
noncomputable def inverseChainOneBodyFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row : NPOracleProgram) (rowFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  bankRegisterCaseOneTargetBitFuel (publishedAmplifier contracts).algorithm row
    (publishedHierarchyOuterPCP contracts clockDepth) machine
    (inverseChainSourceIndex contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (rowFuel (LanguageEvaluationRequest.length request))
    (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
      ((publishedAmplifier contracts).algorithm.outputArity
        (inverseChainAmplifierRequest contracts clockDepth machine
          advantageExponent (LanguageEvaluationRequest.length request)))
      ((publishedAmplifier contracts).algorithm.descriptor
        (inverseChainAmplifierRequest contracts clockDepth machine
          advantageExponent (LanguageEvaluationRequest.length request)))
      (LanguageEvaluationRequest.code request))

/-- Width of the whole chain at one request. -/
noncomputable def inverseChainOneBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (rowBits : ℕ → ℕ → ℕ) (request : LanguageEvaluationRequest) : ℕ :=
  uniformTargetBits (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseChainOneBodyBits contracts clockDepth machine advantageExponent
      rowBits)
    request

/-- Fuel of the whole chain at one request. -/
noncomputable def inverseChainOneFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row : NPOracleProgram) (rowFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  uniformTargetFuel (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (bankRegisterCaseOneTargetBitProgram (publishedAmplifier contracts).algorithm
      (publishedRefuterSource contracts clockDepth).refuter.runner.program row
      machine.description clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent)
    (inverseChainOneBodyFuel contracts clockDepth machine advantageExponent row
      rowFuel)
    request

/-! ## 3. `InverseCaseOnePointRuns`, from the row stage alone -/

/-- **The Case-1 chain's one residual.**  One decision-row stage emitting, at
the schedule's own index and public length, the padded decision row of every
requested randomness code below the scheduled width.  Nothing about the bank,
the amplifier or the target is asked of it. -/
def InverseScheduledRowRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row : NPOracleProgram) (rowBits rowFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (code : ℕ),
    code <
      2 ^ scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseChainSourceIndex contracts clockDepth advantageExponent
          target) →
    runNPOracleProgram row (rowBits target code) (rowFuel target code)
        (initialNPOracleState
          (sourceLength
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          (Nat.pair code
            (Nat.pair
              (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target))
              (encodeBitInput
                (inverseRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target))))) =
      some
        (encodeTaggedList
          (outerProofRowStream
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target) code))

/-- **`InverseCaseOnePointRuns` from the row stage alone.**  Every other
scheduled numeral of the Case-1 chain is now a register read: the source length
by `BankRefuterWordFrameProgram`, the width by `BankOuterProofFormulaSeedProgram`,
and the bank itself by `UniformTargetLanguageBank`.  The onset-restricted
schedule diagonal is threaded, never asserted. -/
theorem inverseCaseOnePointRuns_ofRow
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row : NPOracleProgram) (rowBits rowFuel : ℕ → ℕ → ℕ)
    (hrow :
      InverseScheduledRowRuns contracts clockDepth machine advantageExponent row
        rowBits rowFuel)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target =
        sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)) :
    InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
      (inverseChainOneProgram contracts clockDepth machine advantageExponent row)
      (inverseChainOneBits contracts clockDepth machine advantageExponent
        rowBits)
      (inverseChainOneFuel contracts clockDepth machine advantageExponent row
        rowFuel) := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  rw [inverseCanonicalTargetFunction_caseOne_apply contracts
    (publishedHierarchyOuterPCP contracts clockDepth) machine advantageExponent
    target hlarge hyes hrejects haccepts data hbranch input]
  refine run_uniformTargetProgram (publishedHierarchyOuterPCP contracts
    clockDepth) (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) _ _ _ target input _ ?_
  rw [publishedBankFrame_at_inverseDiagonal contracts clockDepth
    advantageExponent target (encodeBitInput input) (hdiagonal target hlarge)]
  exact run_bankRegisterCaseOneTargetBitProgram
    (publishedAmplifier contracts).algorithm row
    (publishedHierarchyOuterPCP contracts clockDepth) machine
    (inverseChainSourceIndex contracts clockDepth advantageExponent target)
    target _ _ _ (encodeBitInput input) _ _ _ (rowBits target) (rowFuel target)
    (hrow target hlarge)
    (run_targetBitProgram_inverseCaseOne contracts
      (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent target
      (inverseCaseOneTargetOnset_ready contracts
        (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
        target hlarge).1
      data hyes
      (inverseCaseOneTargetOnset_ready contracts
        (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
        target hlarge).2.1
      input)

end NearCubicWires.BankRegisterCaseOneChain

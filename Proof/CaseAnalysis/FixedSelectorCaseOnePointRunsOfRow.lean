import Proof.CaseAnalysis.FixedRegisterCaseOneChain
import Proof.Circuits.FixedSelectorFramedTargetChains
import Proof.Circuits.FixedSelectorHexecutes

/-!
# The fixed Case-1 point run through the selector bank

`FixedRegisterCaseOneChain.fixedCaseOnePointRuns_ofRow` used the old
length-decoded numeral bank and therefore required the false schedule diagonal.
The register-driven Case-1 body itself is frame-parametric.  Prefixing it with
the fixed selector bank supplies its own source length and width registers, so
the same row residual gives the raw point run with no diagonal.
-/

namespace NearCubicWires.FixedSelectorCaseOnePointRunsOfRow

open NearCubicWires
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedRegisterCaseOneChain
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.FixedSelectorFramedTargetChains
open NearCubicWires.FixedSelectorHexecutes
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

open private fixedSelectorBankFrame_eq_raw
  from Proof.Circuits.FixedSelectorFramedTargetChains

/-! ## 1. The selector-prefixed Case-1 chain -/

noncomputable def fixedSelectorChainOneProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (row : NPOracleProgram) : NPOracleProgram :=
  fixedSelectorUniformProgram contracts clockDepth requestedRate
    (bankRegisterCaseOneTargetBitProgram
      (publishedAmplifier contracts).algorithm
      (publishedRefuterSource contracts clockDepth).refuter.runner.program row
      machine.description clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent)

noncomputable def fixedSelectorChainOneBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (rowBits : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  fixedSelectorUniformBits contracts clockDepth requestedRate
    (fixedChainOneBodyBits contracts clockDepth machine requestedRate rowBits)

noncomputable def fixedSelectorChainOneFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (row : NPOracleProgram) (rowFuel : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  fixedSelectorUniformFuel contracts clockDepth requestedRate
    (bankRegisterCaseOneTargetBitProgram
      (publishedAmplifier contracts).algorithm
      (publishedRefuterSource contracts clockDepth).refuter.runner.program row
      machine.description clockDepth
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.shape.coefficient
      (publishedHierarchyOuterPCP contracts clockDepth).proofExponent)
    (fixedChainOneBodyFuel contracts clockDepth machine requestedRate row rowFuel)

/-! ## 2. The raw fixed Case-1 point contract -/

set_option maxHeartbeats 1600000 in
-- The selector frame contains the noncomputable fixed selected source.
/-- The fixed scheduled-row residual supplies the raw Case-1 point run through
the selector bank.  No schedule diagonal is assumed. -/
theorem fixedCaseOnePointRuns_ofSelectorRow
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (row : NPOracleProgram) (rowBits rowFuel : ℕ → ℕ → ℕ)
    (hrow :
      FixedScheduledRowRuns contracts clockDepth machine requestedRate row
        rowBits rowFuel) :
    FixedCaseOnePointRuns contracts clockDepth machine requestedRate
      (fixedSelectorChainOneProgram contracts clockDepth machine requestedRate
        row)
      (fixedSelectorChainOneBits contracts clockDepth machine requestedRate
        rowBits)
      (fixedSelectorChainOneFuel contracts clockDepth machine requestedRate row
        rowFuel) := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  rw [fixedCanonicalTargetFunction_caseOne_apply contracts
    (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
    target hlarge hyes hrejects haccepts data hbranch input]
  refine run_fixedSelectorUniformProgram contracts clockDepth requestedRate _
    (fixedChainOneBodyBits contracts clockDepth machine requestedRate rowBits)
    (fixedChainOneBodyFuel contracts clockDepth machine requestedRate row rowFuel)
    target input _ ?_
  unfold fixedSelectorChainIndex
  rw [fixedSelectorBankFrame_eq_raw]
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

end NearCubicWires.FixedSelectorCaseOnePointRunsOfRow

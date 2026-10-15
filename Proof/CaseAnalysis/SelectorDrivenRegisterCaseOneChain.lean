import Proof.Circuits.SelectorDrivenRegisterTargetChainBase

/-!
# Direct inverse Case-one chain at selector-driven registers

This is the Case-one half of the direct selector-chain join.  The selector
frame already carries the scheduled source length, width, query count, and copy
count, so the register-driven body needs no schedule diagonal.  Its sole
honest residual is `InverseScheduledRowRuns`.
-/

namespace NearCubicWires.SelectorDrivenRegisterCaseOneChain

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

set_option maxHeartbeats 1600000 in
-- The exact output contains the dependent scheduled Case-one witness.
theorem inverse_selectorCaseOneChain_ofRow
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row occurrence : NPOracleProgram)
    (rowBits rowFuel occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (hrow :
      InverseScheduledRowRuns contracts clockDepth machine advantageExponent row
        rowBits rowFuel) :
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
        runNPOracleProgram
            (inverseSelectorCaseOneProgram contracts clockDepth machine row)
            (inverseSelectorDirectChainBits contracts clockDepth machine
              advantageExponent rowBits occurrenceBits ⟨target, input⟩)
            (inverseSelectorDirectChainFuel contracts clockDepth machine
              advantageExponent row occurrence rowFuel occurrenceFuel
              ⟨target, input⟩)
            (initialNPOracleState target
              (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
                ⟨target, input⟩)) =
          some
            (inverseCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target hlarge hyes hrejects haccepts input).toNat := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  rw [inverseCanonicalTargetFunction_caseOne_apply contracts
    (publishedHierarchyOuterPCP contracts clockDepth) machine advantageExponent
    target hlarge hyes hrejects haccepts data hbranch input]
  have hrun :=
    run_bankRegisterCaseOneTargetBitProgram
      (publishedAmplifier contracts).algorithm row
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
        advantageExponent target)
      target
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent target))
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent target)))
      (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent target))
      (encodeBitInput input) _ _ _ (rowBits target) (rowFuel target)
      (hrow target hlarge)
      (run_targetBitProgram_inverseCaseOne contracts
        (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
        target
        (inverseCaseOneTargetOnset_ready contracts
          (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
          target hlarge).1
        data hyes
        (inverseCaseOneTargetOnset_ready contracts
          (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
          target hlarge).2.1
        input)
  unfold inverseSelectorCaseOneProgram inverseSelectorDirectChainBits
    inverseSelectorDirectChainFuel inverseSelectorAdapterFrame
  rw [selectorDrivenBankFrame_eq]
  exact run_fuel_mono (run_bits_mono hrun (Nat.le_max_left _ _))
    (Nat.le_max_left _ _)

end NearCubicWires.SelectorDrivenRegisterCaseOneChain

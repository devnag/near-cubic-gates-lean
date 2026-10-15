import Proof.Circuits.SelectorDrivenRegisterTargetChainBase

/-!
# Direct inverse Case-two chain at selector-driven registers

The generic register-driven Case-two theorem already accepts arbitrary source
length, width, and query-count registers.  Specializing those registers to
`inverseSelectorAdapterFrame` removes the old schedule diagonal.  The only
honest residual is the per-block scheduled occurrence run.
-/

namespace NearCubicWires.SelectorDrivenRegisterCaseTwoChain

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
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
-- The exact output contains the dependent accepting-oracle branch witness.
theorem inverse_selectorCaseTwoChain_ofOccurrence
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (row occurrence : NPOracleProgram)
    (rowBits rowFuel occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (hoccurrence :
      InverseScheduledOccurrenceRuns contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel) :
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
        runNPOracleProgram
            (inverseSelectorCaseTwoProgram contracts occurrence)
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
  intro target hlarge hyes hrejects haccepts branchTwo hbranch input
  rw [inverseCanonicalTargetFunction_caseTwo_apply contracts
    (publishedHierarchyOuterPCP contracts clockDepth) machine advantageExponent
    target hlarge hyes hrejects haccepts branchTwo hbranch input]
  have hrun :=
    run_bankCaseTwoTargetBitProgram
      (publishedAmplifier contracts).algorithm occurrence
      (publishedPointwisePCPP contracts) branchTwo input
      (inverseCaseTwoRawArity_le_target contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target
        (inverseCaseOneTargetOnset_ready contracts
          (publishedHierarchyOuterPCP contracts clockDepth) advantageExponent
          target hlarge).1)
      (sourceLength
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent target))
      (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent target))
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent target)))
      (occurrenceBits target) (occurrenceFuel target)
      (hoccurrence target hlarge hyes branchTwo hbranch input)
  obtain ⟨hbits, hfuel⟩ :=
    inverseCaseTwoBankEnvelopes_ofBranch contracts clockDepth machine
      advantageExponent occurrence occurrenceBits occurrenceFuel target hyes
      branchTwo hbranch input
  unfold inverseSelectorCaseTwoProgram inverseSelectorDirectChainBits
    inverseSelectorDirectChainFuel inverseSelectorAdapterFrame
  rw [selectorDrivenBankFrame_eq]
  exact run_fuel_mono
    (run_bits_mono hrun (hbits.trans (Nat.le_max_right _ _)))
    (hfuel.trans (Nat.le_max_right _ _))

end NearCubicWires.SelectorDrivenRegisterCaseTwoChain

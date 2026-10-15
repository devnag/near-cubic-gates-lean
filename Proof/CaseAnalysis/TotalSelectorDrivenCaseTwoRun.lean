import Proof.Circuits.TotalSelectorDrivenOccurrenceClosure
import Proof.Circuits.SelectorDrivenRegisterTargetChainBase

/-! # Live-branch total selector Case-two run -/

namespace NearCubicWires.TotalSelectorDrivenCaseTwoRun

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

set_option maxRecDepth 2000 in
-- The live Case-two branch carries the complete scheduled packet and maxima.
set_option maxHeartbeats 1600000 in
-- The raw block list and target-bit linker normalize two dependent envelopes.
/-- On a live Case-two branch, the direct selector chain halts with the parity
of the total per-block occurrence outputs.  No target-onset premise is used. -/
theorem run_inverseSelectorCaseTwoProgram_ofTotalOccurrence
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (row occurrence : NPOracleProgram)
    (rowBits rowFuel occurrenceBits occurrenceFuel : ℕ → ℕ → ℕ)
    (hoccurrence :
      TotalInverseScheduledOccurrenceRuns contracts clockDepth machine
        advantageExponent occurrence occurrenceBits occurrenceFuel)
    (target : ℕ)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target))
    (hbranch :
      inverseTargetBranch contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target hyes = .caseTwo caseTwo)
    (point : BitInput target) :
    runNPOracleProgram
        (inverseSelectorCaseTwoProgram contracts occurrence)
        (inverseSelectorDirectChainBits contracts clockDepth machine
          advantageExponent rowBits occurrenceBits ⟨target, point⟩)
        (inverseSelectorDirectChainFuel contracts clockDepth machine
          advantageExponent row occurrence rowFuel occurrenceFuel
          ⟨target, point⟩)
        (initialNPOracleState target
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, point⟩)) =
      some
        (((List.range
          (inverseChainTwoCopies contracts clockDepth advantageExponent
            target)).map
          (caseTwoScheduledBlockValue (publishedPointwisePCPP contracts)
            caseTwo (encodeBitInput point))).foldl xor false).toNat := by
  let copies :=
    inverseChainTwoCopies contracts clockDepth advantageExponent target
  let value :=
    caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
      (encodeBitInput point)
  let bits := (List.range copies).map value
  have hseed :=
    run_bankCaseTwoSeedBlockListProgram occurrence target
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
      copies (encodeBitInput point) (occurrenceBits target)
      (occurrenceFuel target) value
      (fun block hblock =>
        hoccurrence target hyes caseTwo hbranch point block hblock)
  have htarget :=
    run_targetBitProgram_caseTwo (publishedAmplifier contracts).algorithm target
      bits
  have hrun := run_occurrenceStage hseed htarget
  obtain ⟨hbits, hfuel⟩ :=
    inverseCaseTwoBankEnvelopes_ofBranch contracts clockDepth machine
      advantageExponent occurrence occurrenceBits occurrenceFuel target hyes
      caseTwo hbranch point
  unfold inverseSelectorCaseTwoProgram inverseSelectorDirectChainBits
    inverseSelectorDirectChainFuel inverseSelectorAdapterFrame
  rw [selectorDrivenBankFrame_eq]
  exact run_fuel_mono
    (run_bits_mono hrun (hbits.trans (Nat.le_max_right _ _)))
    (hfuel.trans (Nat.le_max_right _ _))

end NearCubicWires.TotalSelectorDrivenCaseTwoRun

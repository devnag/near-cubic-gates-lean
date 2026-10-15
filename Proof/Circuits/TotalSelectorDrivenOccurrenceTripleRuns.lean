import Proof.Circuits.TotalSelectorDrivenOccurrenceContracts

/-! # Onset-free selector occurrence triple -/

namespace NearCubicWires.TotalSelectorDrivenOccurrenceTripleRuns

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorNativeWidth
open NearCubicWires.InverseSelectorOccurrenceEncodingClosure
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoOracleTripleProgram
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts
open NearCubicWires.TotalSelectorDrivenOccurrenceEncodingContracts
open NearCubicWires.VerifiedLinker

set_option maxHeartbeats 1600000 in
-- The dependent oracle triple is quoted in both exact live-branch envelopes.
/-- The selector-computed native width and total substituted encoding supply
the three oracle-derived occurrence numerals without an onset premise. -/
theorem totalInverseScheduledOccurrenceTriple_ofSelectorEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencodings :
      TotalInverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    TotalInverseScheduledOccurrenceTriple contracts clockDepth machine
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel) := by
  intro target hyes caseTwo hbranch
  have harity := run_inverseSelectorNativeWidthProgram contracts clockDepth
    advantageExponent target
  have hencoding := hencodings target hyes caseTwo hbranch
  have hbits :
      inverseSelectorEncodedTripleBits contracts clockDepth machine
          advantageExponent encodingBits target =
        occurrenceStageBits target
          (occurrencePacketPairBits target
            (inverseSelectorNativeWidthBits contracts clockDepth
              advantageExponent target)
            (encodingBits target)
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (BankRegisterCaseOneChain.inverseChainSourceIndex contracts
                  clockDepth advantageExponent target)))
            (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)))
          (oracleTripleBits (publishedPointwisePCPP contracts).factory target
            (caseTwoSubstitutedCircuit caseTwo)) := by
    simp only [inverseSelectorEncodedTripleBits]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseSelectorEncodedTripleFuel contracts clockDepth machine
          advantageExponent encodingProgram encodingFuel target =
        linkFuel (oracleTripleProgram (publishedPointwisePCPP contracts).factory)
          (occurrencePacketPairFuel
            (inverseSelectorNativeWidthProgram contracts clockDepth
              advantageExponent)
            encodingProgram
            (inverseSelectorNativeWidthFuel contracts clockDepth
              advantageExponent target)
            (encodingFuel target))
          (oracleTripleFuel (publishedPointwisePCPP contracts).factory
            (caseTwoSubstitutedCircuit caseTwo)) := by
    simp only [inverseSelectorEncodedTripleFuel]
    rw [dif_pos hyes, hbranch]
  have hword :
      inverseOccurrenceTripleWord contracts clockDepth machine advantageExponent
          target caseTwo =
        oracleTripleWord
          ((publishedPointwisePCPP contracts).factory.forCircuit
            (caseTwoSubstitutedCircuit caseTwo)).clauseBits
          (caseTwoSubstitutedCircuit caseTwo).size
          (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)) := rfl
  have harity' :
      runNPOracleProgram
          (inverseSelectorNativeWidthProgram contracts clockDepth
            advantageExponent)
          (inverseSelectorNativeWidthBits contracts clockDepth
            advantageExponent target)
          (inverseSelectorNativeWidthFuel contracts clockDepth
            advantageExponent target)
          (initialNPOracleState target target) =
        some
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
            (sourceLength
              (BankRegisterCaseOneChain.inverseChainSourceIndex contracts
                clockDepth advantageExponent target))) := by
    simpa [inverseTailSourceLength, inverseTailSourceIndex,
      BankRegisterCaseOneChain.inverseChainSourceIndex] using harity
  rw [hbits, hfuel, hword, inverseSelectorEncodedTripleProgram]
  exact run_occurrenceStage
    (run_occurrencePacketPairProgram
      (inverseSelectorNativeWidthProgram contracts clockDepth advantageExponent)
      encodingProgram target
      (inverseSelectorNativeWidthBits contracts clockDepth advantageExponent
        target)
      (inverseSelectorNativeWidthFuel contracts clockDepth advantageExponent
        target)
      (encodingBits target) (encodingFuel target)
      ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
        (sourceLength
          (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
            advantageExponent target)))
      (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)) harity'
      hencoding)
    (run_oracleTripleProgram (publishedPointwisePCPP contracts).factory target
      (caseTwoSubstitutedCircuit caseTwo))

end NearCubicWires.TotalSelectorDrivenOccurrenceTripleRuns

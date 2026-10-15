import Proof.Circuits.TotalSelectorDrivenOccurrenceTripleRuns

/-! # Onset-free selector occurrence packet -/

namespace NearCubicWires.TotalSelectorDrivenOccurrencePacketRuns

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorOccurrenceQuad
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts

set_option maxHeartbeats 1600000 in
-- The paired packet carries its dependent Case-two oracle in both envelopes.
/-- The selector-computed four-field quad pairs with the onset-free oracle
triple under every live Case-two branch. -/
theorem totalInverseScheduledOccurrencePacket_ofSelectorTriple
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (tripleProgram : NPOracleProgram) (tripleBits tripleFuel : ℕ → ℕ)
    (htriples :
      TotalInverseScheduledOccurrenceTriple contracts clockDepth machine
        advantageExponent tripleProgram tripleBits tripleFuel) :
    TotalInverseScheduledOccurrencePacket contracts clockDepth machine
      advantageExponent
      (inverseSelectorOccurrencePacketProgram contracts clockDepth
        advantageExponent tripleProgram)
      (inverseSelectorOccurrencePacketBits contracts clockDepth machine
        advantageExponent tripleBits)
      (inverseSelectorOccurrencePacketFuel contracts clockDepth
        advantageExponent tripleProgram tripleFuel) := by
  intro target hyes caseTwo hbranch
  have hquad := run_inverseSelectorOccurrenceQuadProgram contracts clockDepth
    advantageExponent target
  have htriple := htriples target hyes caseTwo hbranch
  have hbits :
      inverseSelectorOccurrencePacketBits contracts clockDepth machine
          advantageExponent tripleBits target =
        occurrencePacketPairBits target
          (inverseSelectorOccurrenceQuadBits contracts clockDepth
            advantageExponent target)
          (tripleBits target)
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo) := by
    simp only [inverseSelectorOccurrencePacketBits]
    rw [dif_pos hyes, hbranch]
  have hpacket :
      inverseCaseTwoOccurrencePacket contracts clockDepth machine
          advantageExponent target caseTwo =
        Nat.pair
          (inverseOccurrenceQuadWord contracts clockDepth advantageExponent
            target)
          (inverseOccurrenceTripleWord contracts clockDepth machine
            advantageExponent target caseTwo) := rfl
  rw [hbits, hpacket, inverseSelectorOccurrencePacketProgram,
    inverseSelectorOccurrencePacketFuel]
  exact run_occurrencePacketPairProgram
    (inverseSelectorOccurrenceQuadProgram contracts clockDepth
      advantageExponent)
    tripleProgram target
    (inverseSelectorOccurrenceQuadBits contracts clockDepth advantageExponent
      target)
    (inverseSelectorOccurrenceQuadFuel contracts clockDepth advantageExponent
      target)
    (tripleBits target) (tripleFuel target)
    (inverseOccurrenceQuadWord contracts clockDepth advantageExponent target)
    (inverseOccurrenceTripleWord contracts clockDepth machine advantageExponent
      target caseTwo)
    hquad htriple

end NearCubicWires.TotalSelectorDrivenOccurrencePacketRuns

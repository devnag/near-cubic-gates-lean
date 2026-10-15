import Proof.Circuits.TotalSelectorDrivenOccurrenceCalleeRuns

/-! # Complete onset-free selector occurrence closure -/

namespace NearCubicWires.TotalSelectorDrivenOccurrenceClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorOccurrenceEncodingClosure
open NearCubicWires.InverseSelectorOccurrenceQuad
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.TotalSelectorDrivenAtomStreamContract
open NearCubicWires.TotalSelectorDrivenCircuitEncodingRuns
open NearCubicWires.TotalSelectorDrivenOccurrenceCalleeRuns
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts
open NearCubicWires.TotalSelectorDrivenOccurrenceEncodingContracts
open NearCubicWires.TotalSelectorDrivenOccurrenceEncodingRuns
open NearCubicWires.TotalSelectorDrivenOccurrencePacketRuns
open NearCubicWires.TotalSelectorDrivenOccurrenceTripleRuns

set_option maxHeartbeats 1600000 in
-- The closed atom-stream tower expands three dependent executable stages.
/-- A total description atom stream supplies the complete substituted-circuit
encoding under every live Case-two branch. -/
theorem totalInverseScheduledOccurrenceEncoding_ofAtomStream
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      TotalInverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    TotalInverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSelectorClosedEncodingProgram contracts clockDepth machine
        advantageExponent stream)
      (inverseSelectorClosedEncodingBits contracts clockDepth machine
        advantageExponent streamBits)
      (inverseSelectorClosedEncodingFuel contracts clockDepth machine
        advantageExponent stream streamFuel) := by
  have hframe := totalInverseDescriptionFrameRuns_ofAtomStream contracts
    clockDepth machine advantageExponent stream streamBits streamFuel hstream
  have hcircuits := totalInverseScheduledCircuitEncoding_ofDecoder contracts
    clockDepth machine advantageExponent (inverseDescriptionFrameProgram stream)
    canonicalDescriptionDecoderProgram
    (inverseDescriptionFrameBits contracts clockDepth machine advantageExponent
      streamBits)
    (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
      streamFuel)
    canonicalDescriptionDecoderBits canonicalDescriptionDecoderFuel hframe
    canonicalDescriptionDecoder_holds
  exact totalInverseScheduledOccurrenceEncoding_ofCircuitEncoding contracts
    clockDepth machine advantageExponent
    (inverseCircuitEncodingProgram (inverseDescriptionFrameProgram stream)
      canonicalDescriptionDecoderProgram)
    (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
      canonicalDescriptionDecoderBits
      (inverseDescriptionFrameBits contracts clockDepth machine
        advantageExponent streamBits))
    (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
      canonicalDescriptionDecoderProgram canonicalDescriptionDecoderFuel
      (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
        streamFuel))
    hcircuits

set_option maxRecDepth 2000 in
-- The final occurrence program expands the packet and callee resource tower.
set_option maxHeartbeats 1600000 in
-- The assembled occurrence runner expands the triple and seven-field packet.
/-- A total substituted encoding supplies the complete per-block occurrence
callee under every live Case-two branch. -/
theorem totalInverseScheduledOccurrenceRuns_ofSelectorEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencodings :
      TotalInverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    TotalInverseScheduledOccurrenceRuns contracts clockDepth machine
      advantageExponent
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel) := by
  have htriples :=
    totalInverseScheduledOccurrenceTriple_ofSelectorEncoding contracts
      clockDepth machine advantageExponent encodingProgram encodingBits
      encodingFuel hencodings
  have hpackets :=
    totalInverseScheduledOccurrencePacket_ofSelectorTriple contracts clockDepth
      machine advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel)
      htriples
  exact totalInverseScheduledOccurrenceRuns_ofPacket contracts clockDepth
    machine advantageExponent
    (inverseSelectorOccurrencePacketProgram contracts clockDepth
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram))
    (inverseSelectorOccurrencePacketBits contracts clockDepth machine
      advantageExponent
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits))
    (inverseSelectorOccurrencePacketFuel contracts clockDepth advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel))
    hpackets

end NearCubicWires.TotalSelectorDrivenOccurrenceClosure

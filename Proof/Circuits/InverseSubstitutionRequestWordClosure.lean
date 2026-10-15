import Proof.Circuits.InverseSubstitutionRequestTail
import Proof.MachineModel.RuntimeCaseTwoCircuitEncodingClosure
import Proof.MachineModel.RuntimeCaseTwoDescriptionFrameAdapter

/-!
# The inverse substitution request word, without a schedule diagonal

The recovered oracle's circuit-code stream is paired with the selector-driven
three-field tail.  The tail computes its native width, scheduled source length,
and refuter word from the public target itself, so the old diagonal premise is
not needed.
-/

namespace NearCubicWires.InverseSubstitutionRequestWordClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.InverseSubstitutionRequestTail
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure

noncomputable def inverseSubstitutionRequestWordProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (circuitProgram : NPOracleProgram) :
    NPOracleProgram :=
  occurrencePacketPairProgram circuitProgram
    (inverseSubstitutionRequestTailProgram contracts clockDepth machine
      advantageExponent)

open Classical in
noncomputable def inverseSubstitutionRequestWordBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (circuitBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  if hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))
        (inverseRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          advantageExponent target) then
    match inverseTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target hyes with
    | .caseOne _ => 0
    | .caseTwo caseTwo =>
        occurrencePacketPairBits target (circuitBits target)
          (inverseSubstitutionRequestTailBits contracts clockDepth machine
            advantageExponent target)
          (encodeBooleanCircuit caseTwo.circuit)
          (Nat.pair
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (inverseTailSourceLength contracts clockDepth advantageExponent
                target))
            (Nat.pair
              (inverseTailSourceLength contracts clockDepth advantageExponent
                target)
              (inverseTailRefuterCode contracts clockDepth machine
                advantageExponent target)))
  else 0

noncomputable def inverseSubstitutionRequestWordFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (circuitProgram : NPOracleProgram)
    (circuitFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrencePacketPairFuel circuitProgram
    (inverseSubstitutionRequestTailProgram contracts clockDepth machine
      advantageExponent)
    (circuitFuel target)
    (inverseSubstitutionRequestTailFuel contracts clockDepth machine
      advantageExponent target)

set_option maxHeartbeats 800000 in
-- The paired dependent request word appears in both branch envelopes.
theorem inverseSubstitutionRequestWord_ofCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ)
    (hcircuits :
      InverseScheduledCircuitEncoding contracts clockDepth machine
        advantageExponent circuitProgram circuitBits circuitFuel) :
    InverseSubstitutionRequestWord contracts clockDepth machine
      advantageExponent
      (inverseSubstitutionRequestWordProgram contracts clockDepth machine
        advantageExponent circuitProgram)
      (inverseSubstitutionRequestWordBits contracts clockDepth machine
        advantageExponent circuitBits)
      (inverseSubstitutionRequestWordFuel contracts clockDepth machine
        advantageExponent circuitProgram circuitFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have hcircuit := hcircuits target hlarge hyes caseTwo hbranch
  have htail := run_inverseSubstitutionRequestTailProgram contracts clockDepth
    machine advantageExponent target
  have hbits :
      inverseSubstitutionRequestWordBits contracts clockDepth machine
          advantageExponent circuitBits target =
        occurrencePacketPairBits target (circuitBits target)
          (inverseSubstitutionRequestTailBits contracts clockDepth machine
            advantageExponent target)
          (encodeBooleanCircuit caseTwo.circuit)
          (Nat.pair
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (inverseTailSourceLength contracts clockDepth advantageExponent
                target))
            (Nat.pair
              (inverseTailSourceLength contracts clockDepth advantageExponent
                target)
              (inverseTailRefuterCode contracts clockDepth machine
                advantageExponent target))) := by
    simp only [inverseSubstitutionRequestWordBits]
    rw [dif_pos hyes, hbranch]
  rw [hbits, inverseSubstitutionRequestWordProgram,
    inverseSubstitutionRequestWordFuel]
  simpa [inverseTailSourceLength, inverseTailSourceIndex,
      inverseTailRefuterCode, BankRegisterCaseOneChain.inverseChainSourceIndex]
    using
      (run_occurrencePacketPairProgram circuitProgram
        (inverseSubstitutionRequestTailProgram contracts clockDepth machine
          advantageExponent)
        target (circuitBits target) (circuitFuel target)
        (inverseSubstitutionRequestTailBits contracts clockDepth machine
          advantageExponent target)
        (inverseSubstitutionRequestTailFuel contracts clockDepth machine
          advantageExponent target)
        (encodeBooleanCircuit caseTwo.circuit)
        (Nat.pair
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target))
          (Nat.pair
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target)
            (inverseTailRefuterCode contracts clockDepth machine
              advantageExponent target)))
        hcircuit htail)

set_option maxHeartbeats 1600000 in
-- The linked substituted encoder expands the full dependent Case-2 request.
/-- The substituted-circuit encoding follows from the recovered oracle's own
circuit code, with every request-tail numeral computed by the selector. -/
theorem inverseScheduledOccurrenceEncoding_ofCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ)
    (hcircuits :
      InverseScheduledCircuitEncoding contracts clockDepth machine
        advantageExponent circuitProgram circuitBits circuitFuel) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSubstitutedEncodingProgram contracts clockDepth
        (inverseSubstitutionRequestWordProgram contracts clockDepth machine
          advantageExponent circuitProgram))
      (inverseSubstitutedEncodingBits contracts clockDepth machine
        advantageExponent
        (inverseSubstitutionRequestWordBits contracts clockDepth machine
          advantageExponent circuitBits))
      (inverseSubstitutedEncodingFuel contracts clockDepth machine
        advantageExponent
        (inverseSubstitutionRequestWordFuel contracts clockDepth machine
          advantageExponent circuitProgram circuitFuel)) :=
  inverseScheduledOccurrenceEncoding_ofRequestWord contracts clockDepth machine
    advantageExponent
    (inverseSubstitutionRequestWordProgram contracts clockDepth machine
      advantageExponent circuitProgram)
    (inverseSubstitutionRequestWordBits contracts clockDepth machine
      advantageExponent circuitBits)
    (inverseSubstitutionRequestWordFuel contracts clockDepth machine
      advantageExponent circuitProgram circuitFuel)
    (inverseSubstitutionRequestWord_ofCircuitEncoding contracts clockDepth
      machine advantageExponent circuitProgram circuitBits circuitFuel
      hcircuits)

set_option maxHeartbeats 1600000 in
-- The decoder statement carries both linked resource families at one branch.
/-- A description-frame program and the published grouping decoder now suffice
for the complete substituted-circuit encoding; no schedule diagonal remains. -/
theorem inverseScheduledOccurrenceEncoding_ofDecoder
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (adapter decoder : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ)
    (decoderBits decoderFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseDescriptionFrameRuns contracts clockDepth machine advantageExponent
        adapter adapterBits adapterFuel)
    (hdecoder : CanonicalDescriptionDecoder decoder decoderBits decoderFuel) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSubstitutedEncodingProgram contracts clockDepth
        (inverseSubstitutionRequestWordProgram contracts clockDepth machine
          advantageExponent (inverseCircuitEncodingProgram adapter decoder)))
      (inverseSubstitutedEncodingBits contracts clockDepth machine
        advantageExponent
        (inverseSubstitutionRequestWordBits contracts clockDepth machine
          advantageExponent
          (inverseCircuitEncodingBits contracts clockDepth machine
            advantageExponent decoderBits adapterBits)))
      (inverseSubstitutedEncodingFuel contracts clockDepth machine
        advantageExponent
        (inverseSubstitutionRequestWordFuel contracts clockDepth machine
          advantageExponent (inverseCircuitEncodingProgram adapter decoder)
          (inverseCircuitEncodingFuel contracts clockDepth machine
            advantageExponent decoder decoderFuel adapterFuel))) :=
  inverseScheduledOccurrenceEncoding_ofCircuitEncoding contracts clockDepth
    machine advantageExponent (inverseCircuitEncodingProgram adapter decoder)
    (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
      decoderBits adapterBits)
    (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
      decoder decoderFuel adapterFuel)
    (RuntimeCaseTwoCircuitEncodingClosure.inverseScheduledCircuitEncoding_ofDecoder
      contracts clockDepth machine advantageExponent adapter decoder adapterBits
      adapterFuel decoderBits decoderFuel hadapter hdecoder)

/-! ## The closed encoder at one supplied atom stream -/

noncomputable def inverseSelectorClosedEncodingProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (stream : NPOracleProgram) : NPOracleProgram :=
  inverseSubstitutedEncodingProgram contracts clockDepth
    (inverseSubstitutionRequestWordProgram contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingProgram (inverseDescriptionFrameProgram stream)
        canonicalDescriptionDecoderProgram))

noncomputable def inverseSelectorClosedEncodingBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (streamBits : ℕ → ℕ) : ℕ → ℕ :=
  inverseSubstitutedEncodingBits contracts clockDepth machine advantageExponent
    (inverseSubstitutionRequestWordBits contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
        canonicalDescriptionDecoderBits
        (inverseDescriptionFrameBits contracts clockDepth machine
          advantageExponent streamBits)))

noncomputable def inverseSelectorClosedEncodingFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (stream : NPOracleProgram)
    (streamFuel : ℕ → ℕ) : ℕ → ℕ :=
  inverseSubstitutedEncodingFuel contracts clockDepth machine advantageExponent
    (inverseSubstitutionRequestWordFuel contracts clockDepth machine
      advantageExponent
      (inverseCircuitEncodingProgram (inverseDescriptionFrameProgram stream)
        canonicalDescriptionDecoderProgram)
      (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
        canonicalDescriptionDecoderProgram canonicalDescriptionDecoderFuel
        (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
          streamFuel)))

set_option maxHeartbeats 1600000 in
-- The closed atom-stream tower expands all three linked executable stages.
/-- The atom stream is now the sole executable residual below the substituted
circuit encoding; the selector computes every dependent request numeral. -/
theorem inverseScheduledOccurrenceEncoding_ofAtomStream
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      InverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSelectorClosedEncodingProgram contracts clockDepth machine
        advantageExponent stream)
      (inverseSelectorClosedEncodingBits contracts clockDepth machine
        advantageExponent streamBits)
      (inverseSelectorClosedEncodingFuel contracts clockDepth machine
        advantageExponent stream streamFuel) := by
  exact inverseScheduledOccurrenceEncoding_ofDecoder contracts clockDepth
    machine advantageExponent (inverseDescriptionFrameProgram stream)
    canonicalDescriptionDecoderProgram
    (inverseDescriptionFrameBits contracts clockDepth machine advantageExponent
      streamBits)
    (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
      streamFuel)
    canonicalDescriptionDecoderBits canonicalDescriptionDecoderFuel
    (inverseDescriptionFrameRuns_ofAtomStream contracts clockDepth machine
      advantageExponent stream streamBits streamFuel hstream)
    canonicalDescriptionDecoder_holds

end NearCubicWires.InverseSubstitutionRequestWordClosure

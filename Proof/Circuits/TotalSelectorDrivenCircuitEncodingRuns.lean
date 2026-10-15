import Proof.Circuits.TotalSelectorDrivenCircuitEncodingContracts

/-! # Onset-free selector circuit-encoding runs -/

namespace NearCubicWires.TotalSelectorDrivenCircuitEncodingRuns

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CanonicalDescriptionGroupingDecoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.ScheduledRecovery
open NearCubicWires.TotalSelectorDrivenAtomStreamContract
open NearCubicWires.TotalSelectorDrivenCircuitEncodingContracts
open NearCubicWires.VerifiedLinker

/-- A total atom stream yields its computed description frame at every target.
-/
theorem totalInverseDescriptionFrameRuns_ofAtomStream
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ)
    (hstream :
      TotalInverseDescriptionAtomStreamRuns contracts clockDepth machine
        advantageExponent stream streamBits streamFuel) :
    TotalInverseDescriptionFrameRuns contracts clockDepth machine
      advantageExponent (inverseDescriptionFrameProgram stream)
      (inverseDescriptionFrameBits contracts clockDepth machine
        advantageExponent streamBits)
      (inverseDescriptionFrameFuel contracts clockDepth advantageExponent
        streamFuel) := by
  intro target
  rw [canonicalCircuitEncoderInput_eq contracts clockDepth machine
    advantageExponent target]
  exact run_occurrenceStage (hstream target)
    (run_descriptionFrameWidthProgram target
      (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
      (inverseFrameWidth contracts clockDepth advantageExponent target)
      (inverseFrameBound contracts clockDepth advantageExponent target))

set_option maxHeartbeats 800000 in
-- The statement carries the linked encoder and both live-branch envelopes.
/-- Under a live Case-two branch, a total description frame and the canonical
decoder emit the recovered oracle's circuit code without an onset argument. -/
theorem totalInverseScheduledCircuitEncoding_ofDecoder
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (adapter decoder : NPOracleProgram) (adapterBits adapterFuel : ℕ → ℕ)
    (decoderBits decoderFuel : ℕ → ℕ → ℕ)
    (hadapter :
      TotalInverseDescriptionFrameRuns contracts clockDepth machine
        advantageExponent adapter adapterBits adapterFuel)
    (hdecoder : CanonicalDescriptionDecoder decoder decoderBits decoderFuel) :
    TotalInverseScheduledCircuitEncoding contracts clockDepth machine
      advantageExponent (inverseCircuitEncodingProgram adapter decoder)
      (inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
        decoderBits adapterBits)
      (inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
        decoder decoderFuel adapterFuel) := by
  intro target hyes caseTwo hbranch
  have hframe := hadapter target
  have hencoder :=
    run_canonicalCircuitEncoderProgram
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)
      caseTwo decoder decoderBits decoderFuel hdecoder target
  have hbits :
      inverseCircuitEncodingBits contracts clockDepth machine advantageExponent
          decoderBits adapterBits target =
        occurrenceStageBits target (adapterBits target)
          (canonicalCircuitEncoderBits
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo decoderBits target) := by
    simp only [inverseCircuitEncodingBits]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseCircuitEncodingFuel contracts clockDepth machine advantageExponent
          decoder decoderFuel adapterFuel target =
        linkFuel (canonicalCircuitEncoderProgram decoder) (adapterFuel target)
          (canonicalCircuitEncoderFuel
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo decoder decoderFuel target) := by
    simp only [inverseCircuitEncodingFuel]
    rw [dif_pos hyes, hbranch]
  rw [hbits, hfuel, inverseCircuitEncodingProgram]
  exact run_occurrenceStage hframe hencoder

end NearCubicWires.TotalSelectorDrivenCircuitEncodingRuns

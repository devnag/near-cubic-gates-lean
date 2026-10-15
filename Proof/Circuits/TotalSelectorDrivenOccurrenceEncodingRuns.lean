import Proof.Circuits.TotalSelectorDrivenOccurrenceEncodingContracts

/-! # Onset-free selector occurrence-encoding runs -/

namespace NearCubicWires.TotalSelectorDrivenOccurrenceEncodingRuns

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSubstitutedCircuitEncoder
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.InverseSubstitutionRequestTail
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.TotalSelectorDrivenCircuitEncodingContracts
open NearCubicWires.TotalSelectorDrivenOccurrenceEncodingContracts
open NearCubicWires.VerifiedLinker

open private inverseNativeWidthLe from
  Proof.MachineModel.RuntimeCaseTwoSubstitutedEncodingClosure

set_option maxRecDepth 2000 in
-- The selector request and substituted circuit are deeply paired values.
set_option maxHeartbeats 800000 in
-- The paired dependent selector request appears in both live-branch envelopes.
/-- The selector-computed request tail pairs with a total recovered circuit
encoding under every live Case-two branch. -/
theorem totalInverseSubstitutionRequestWord_ofCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ)
    (hcircuits :
      TotalInverseScheduledCircuitEncoding contracts clockDepth machine
        advantageExponent circuitProgram circuitBits circuitFuel) :
    TotalInverseSubstitutionRequestWord contracts clockDepth machine
      advantageExponent
      (inverseSubstitutionRequestWordProgram contracts clockDepth machine
        advantageExponent circuitProgram)
      (inverseSubstitutionRequestWordBits contracts clockDepth machine
        advantageExponent circuitBits)
      (inverseSubstitutionRequestWordFuel contracts clockDepth machine
        advantageExponent circuitProgram circuitFuel) := by
  intro target hyes caseTwo hbranch
  have hcircuit := hcircuits target hyes caseTwo hbranch
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

set_option maxRecDepth 2000 in
-- The live branch output contains the complete substituted circuit encoding.
set_option maxHeartbeats 400000 in
-- The statement carries the linked substituted encoder and live branch read.
/-- Restriction, substitution, and arity padding preserve the onset-free live
Case-two request-word contract. -/
theorem totalInverseScheduledOccurrenceEncoding_ofRequestWord
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (requestProgram : NPOracleProgram) (requestBits requestFuel : ℕ → ℕ)
    (hrequests :
      TotalInverseSubstitutionRequestWord contracts clockDepth machine
        advantageExponent requestProgram requestBits requestFuel) :
    TotalInverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseSubstitutedEncodingProgram contracts clockDepth requestProgram)
      (inverseSubstitutedEncodingBits contracts clockDepth machine
        advantageExponent requestBits)
      (inverseSubstitutedEncodingFuel contracts clockDepth machine
        advantageExponent requestFuel) := by
  intro target hyes caseTwo hbranch
  have hrequest := hrequests target hyes caseTwo hbranch
  have hbits :
      inverseSubstitutedEncodingBits contracts clockDepth machine
          advantageExponent requestBits target =
        occurrenceStageBits target (requestBits target)
          (substitutedEncodingBits
            (publishedHierarchyOuterPCP contracts clockDepth).substitution
            target
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo.circuit
            (inverseNativeWidthLe contracts clockDepth advantageExponent
              target)) := by
    simp only [inverseSubstitutedEncodingBits]
    rw [dif_pos hyes, hbranch]
  have hfuel :
      inverseSubstitutedEncodingFuel contracts clockDepth machine
          advantageExponent requestFuel target =
        linkFuel
          (substitutedEncodingProgram
            (publishedHierarchyOuterPCP contracts
              clockDepth).substitution.runner.program)
          (requestFuel target)
          (substitutedEncodingFuel
            (publishedHierarchyOuterPCP contracts clockDepth).substitution
            target
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            caseTwo.circuit
            (inverseNativeWidthLe contracts clockDepth advantageExponent
              target)) := by
    simp only [inverseSubstitutedEncodingFuel]
    rw [dif_pos hyes, hbranch]
  have htarget :
      encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo) =
        encodeBooleanCircuit
          ((publishedHierarchyOuterPCP contracts clockDepth).substitution.circuit
            (substRequest
              (inverseRefuterInput contracts
                (publishedHierarchyOuterPCP contracts clockDepth) machine
                advantageExponent target)
              caseTwo.circuit
              (inverseNativeWidthLe contracts clockDepth advantageExponent
                target))).padToArity :=
    rfl
  rw [hbits, hfuel, htarget, inverseSubstitutedEncodingProgram]
  exact run_occurrenceStage hrequest
    (run_substitutedEncodingProgram
      (publishedHierarchyOuterPCP contracts clockDepth).substitution target
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent target)
      caseTwo.circuit
      (inverseNativeWidthLe contracts clockDepth advantageExponent target))

set_option maxHeartbeats 1600000 in
-- The convenience theorem expands the complete selector request-word ABI.
/-- The complete substituted encoder follows directly from a total recovered
circuit stream. -/
theorem totalInverseScheduledOccurrenceEncoding_ofCircuitEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (circuitProgram : NPOracleProgram) (circuitBits circuitFuel : ℕ → ℕ)
    (hcircuits :
      TotalInverseScheduledCircuitEncoding contracts clockDepth machine
        advantageExponent circuitProgram circuitBits circuitFuel) :
    TotalInverseScheduledOccurrenceEncoding contracts clockDepth machine
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
  totalInverseScheduledOccurrenceEncoding_ofRequestWord contracts clockDepth
    machine advantageExponent
    (inverseSubstitutionRequestWordProgram contracts clockDepth machine
      advantageExponent circuitProgram)
    (inverseSubstitutionRequestWordBits contracts clockDepth machine
      advantageExponent circuitBits)
    (inverseSubstitutionRequestWordFuel contracts clockDepth machine
      advantageExponent circuitProgram circuitFuel)
    (totalInverseSubstitutionRequestWord_ofCircuitEncoding contracts clockDepth
      machine advantageExponent circuitProgram circuitBits circuitFuel
      hcircuits)

end NearCubicWires.TotalSelectorDrivenOccurrenceEncodingRuns

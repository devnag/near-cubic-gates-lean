import Proof.Circuits.TotalSelectorDrivenOccurrencePacketRuns

/-! # Onset-free selector per-block occurrence callee -/

namespace NearCubicWires.TotalSelectorDrivenOccurrenceCalleeRuns

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.TotalSelectorDrivenOccurrenceContracts
open NearCubicWires.VerifiedLinker

open private run_fuel_mono from Proof.MachineModel.RuntimeCaseTwoOccurrenceClosure

set_option maxHeartbeats 1600000 in
-- The callee proof carries the packet and both live-branch resource envelopes.
/-- Reading the total seven-field packet makes the per-block occurrence callee
run under every live Case-two branch, without an onset argument. -/
theorem totalInverseScheduledOccurrenceRuns_ofPacket
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (packetProgram : NPOracleProgram) (packetBits packetFuel : ℕ → ℕ)
    (hpackets :
      TotalInverseScheduledOccurrencePacket contracts clockDepth machine
        advantageExponent packetProgram packetBits packetFuel) :
    TotalInverseScheduledOccurrenceRuns contracts clockDepth machine
      advantageExponent
      (occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
        packetProgram)
      (inverseOccurrenceBranchBits contracts clockDepth machine
        advantageExponent packetBits)
      (inverseOccurrenceBranchFuel contracts clockDepth machine
        advantageExponent packetProgram packetFuel) := by
  intro target hyes caseTwo hbranch point block _hblock
  have hpacket := hpackets target hyes caseTwo hbranch
  have hrun :=
    run_occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
      packetProgram target
      (inverseCaseTwoOccurrencePacket contracts clockDepth machine
        advantageExponent target caseTwo)
      (packetBits target) (packetFuel target)
      (caseTwoSubstitutedCircuit caseTwo) block (encodeBitInput point) hpacket
      (by simp [inverseCaseTwoOccurrencePacket, inverseChainSourceIndex])
      (by simp [inverseCaseTwoOccurrencePacket])
      (by simp [inverseCaseTwoOccurrencePacket])
  have hvalue :
      (caseTwoBlockValue (publishedPointwisePCPP contracts).factory
          (caseTwoSubstitutedCircuit caseTwo)
          (packetInputArity
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetPaddedInputBits
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetNativeClauseBits
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetPaddedClauseBits
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (packetArity
            (inverseCaseTwoOccurrencePacket contracts clockDepth machine
              advantageExponent target caseTwo))
          (encodeBitInput point) block) =
        caseTwoScheduledBlockValue (publishedPointwisePCPP contracts) caseTwo
          (encodeBitInput point) block := by
    simp [inverseCaseTwoOccurrencePacket, caseTwoScheduledBlockValue,
      inverseChainSourceIndex]
  rw [hvalue] at hrun
  have hmember :
      encodeBitInput point ∈ Finset.range (2 ^ target) :=
    Finset.mem_range.mpr (encodeBitInput_lt_pow point)
  have hbitsEq :
      inverseOccurrenceBranchBits contracts clockDepth machine advantageExponent
          packetBits target block =
        (Finset.range (2 ^ target)).sup
          (inverseOccurrenceCaseTwoBits contracts clockDepth machine
            advantageExponent packetBits target caseTwo block) := by
    simp only [inverseOccurrenceBranchBits]
    rw [dif_pos hyes, hbranch]
  have hfuelEq :
      inverseOccurrenceBranchFuel contracts clockDepth machine advantageExponent
          packetProgram packetFuel target block =
        (Finset.range (2 ^ target)).sup
          (inverseOccurrenceCaseTwoFuel contracts clockDepth machine
            advantageExponent packetProgram packetFuel target caseTwo block) := by
    simp only [inverseOccurrenceBranchFuel]
    rw [dif_pos hyes, hbranch]
  have hbitsLe :=
    Finset.le_sup
      (f :=
        inverseOccurrenceCaseTwoBits contracts clockDepth machine
          advantageExponent packetBits target caseTwo block)
      hmember
  have hfuelLe :=
    Finset.le_sup
      (f :=
        inverseOccurrenceCaseTwoFuel contracts clockDepth machine
          advantageExponent packetProgram packetFuel target caseTwo block)
      hmember
  rw [inverseOccurrenceCaseTwoBits] at hbitsLe
  rw [inverseOccurrenceCaseTwoFuel] at hfuelLe
  exact run_fuel_mono
    (run_bits_mono hrun (hbitsEq ▸ hbitsLe))
    (hfuelEq ▸ hfuelLe)

end NearCubicWires.TotalSelectorDrivenOccurrenceCalleeRuns

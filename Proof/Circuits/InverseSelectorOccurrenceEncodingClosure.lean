import Proof.Circuits.InverseSelectorOccurrenceQuad
import Proof.Circuits.InverseSelectorNativeWidth
import Proof.Circuits.InverseSubstitutionRequestWordClosure
import Proof.MachineModel.RuntimeCaseTwoOracleTripleProgram

/-!
# The inverse Case-2 occurrence runner from one encoding stream

The selector-driven native-width stream turns a substituted-circuit encoding
into the oracle triple.  The selector-driven occurrence quad then supplies the
other four packet fields.  Consequently the complete occurrence callee no
longer needs a public-target/scheduled-length diagonal.
-/

namespace NearCubicWires.InverseSelectorOccurrenceEncodingClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorNativeWidth
open NearCubicWires.InverseSelectorOccurrenceQuad
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoOracleTripleProgram
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

noncomputable def inverseSelectorEncodedTripleProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (encodingProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms
    (occurrencePacketPairProgram
      (inverseSelectorNativeWidthProgram contracts clockDepth advantageExponent)
      encodingProgram)
    (oracleTripleProgram (publishedPointwisePCPP contracts).factory)

open Classical in
noncomputable def inverseSelectorEncodedTripleBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (encodingBits : ℕ → ℕ) (target : ℕ) : ℕ :=
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
        occurrenceStageBits target
          (occurrencePacketPairBits target
            (inverseSelectorNativeWidthBits contracts clockDepth
              advantageExponent target)
            (encodingBits target)
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
              (sourceLength
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target)))
            (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)))
          (oracleTripleBits (publishedPointwisePCPP contracts).factory target
            (caseTwoSubstitutedCircuit caseTwo))
  else 0

open Classical in
noncomputable def inverseSelectorEncodedTripleFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (encodingProgram : NPOracleProgram)
    (encodingFuel : ℕ → ℕ) (target : ℕ) : ℕ :=
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
        linkFuel (oracleTripleProgram (publishedPointwisePCPP contracts).factory)
          (occurrencePacketPairFuel
            (inverseSelectorNativeWidthProgram contracts clockDepth
              advantageExponent)
            encodingProgram
            (inverseSelectorNativeWidthFuel contracts clockDepth
              advantageExponent target)
            (encodingFuel target))
          (oracleTripleFuel (publishedPointwisePCPP contracts).factory
            (caseTwoSubstitutedCircuit caseTwo))
  else 0

set_option maxHeartbeats 1600000 in
-- The dependent oracle triple is quoted in both exact resource envelopes.
theorem inverseScheduledOccurrenceTriple_ofSelectorEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencodings :
      InverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    InverseScheduledOccurrenceTriple contracts clockDepth machine
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel) := by
  intro target hlarge hyes caseTwo hbranch
  have harity := run_inverseSelectorNativeWidthProgram contracts clockDepth
    advantageExponent target
  have hencoding := hencodings target hlarge hyes caseTwo hbranch
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
                (inverseChainSourceIndex contracts clockDepth advantageExponent
                  target)))
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
              (inverseChainSourceIndex contracts clockDepth advantageExponent
                target))) := by
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
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target)))
      (encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)) harity'
      hencoding)
    (run_oracleTripleProgram (publishedPointwisePCPP contracts).factory target
      (caseTwoSubstitutedCircuit caseTwo))

/-! ## Complete occurrence runner -/

noncomputable def inverseSelectorOccurrenceProgramOfEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (encodingProgram : NPOracleProgram) :
    NPOracleProgram :=
  occurrenceCalleeProgram (publishedPointwisePCPP contracts).factory
    (inverseSelectorOccurrencePacketProgram contracts clockDepth
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram))

noncomputable def inverseSelectorOccurrenceBitsOfEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (encodingBits : ℕ → ℕ) : ℕ → ℕ → ℕ :=
  inverseOccurrenceBranchBits contracts clockDepth machine advantageExponent
    (inverseSelectorOccurrencePacketBits contracts clockDepth machine
      advantageExponent
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits))

noncomputable def inverseSelectorOccurrenceFuelOfEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (encodingProgram : NPOracleProgram)
    (encodingFuel : ℕ → ℕ) : ℕ → ℕ → ℕ :=
  inverseOccurrenceBranchFuel contracts clockDepth machine advantageExponent
    (inverseSelectorOccurrencePacketProgram contracts clockDepth
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram))
    (inverseSelectorOccurrencePacketFuel contracts clockDepth
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel))

set_option maxHeartbeats 1600000 in
-- The assembled occurrence runner expands the triple and seven-field packet.
theorem inverseScheduledOccurrenceRuns_ofSelectorEncoding
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (encodingProgram : NPOracleProgram) (encodingBits encodingFuel : ℕ → ℕ)
    (hencodings :
      InverseScheduledOccurrenceEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingBits encodingFuel) :
    InverseScheduledOccurrenceRuns contracts clockDepth machine
      advantageExponent
      (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel) := by
  have htriples :=
    inverseScheduledOccurrenceTriple_ofSelectorEncoding contracts clockDepth
      machine advantageExponent encodingProgram encodingBits encodingFuel
      hencodings
  have hpackets :=
    inverseScheduledOccurrencePacket_ofSelectorTriple contracts clockDepth
      machine advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel)
      htriples
  exact inverseScheduledOccurrenceRuns_ofPacket contracts clockDepth machine
    advantageExponent
    (inverseSelectorOccurrencePacketProgram contracts clockDepth
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram))
    (inverseSelectorOccurrencePacketBits contracts clockDepth machine
      advantageExponent
      (inverseSelectorEncodedTripleBits contracts clockDepth machine
        advantageExponent encodingBits))
    (inverseSelectorOccurrencePacketFuel contracts clockDepth
      advantageExponent
      (inverseSelectorEncodedTripleProgram contracts clockDepth
        advantageExponent encodingProgram)
      (inverseSelectorEncodedTripleFuel contracts clockDepth machine
        advantageExponent encodingProgram encodingFuel))
    hpackets

end NearCubicWires.InverseSelectorOccurrenceEncodingClosure

import Proof.Hierarchy.CompetitorWitnessHeaderReady

/-! The actual cold header receipt exposes the two exact typed canonical
payloads and the union-family flag of the same guessed witness. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalBinary CanonicalWitnessCodec SupplierPipeline ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def witnessOracle {limits : RecoveryWitnessLimits} : CheckedRecoveryWitness limits → BooleanCircuit limits.oracleArity
  | .symmetric oracle _ _=>oracle
  | .threshold oracle _ _=>oracle
def witnessSumCode {limits : RecoveryWitnessLimits} : CheckedRecoveryWitness limits → ℕ
  | .symmetric _ _ sum=>sum.code symmetricCircuitCodec
  | .threshold _ _ sum=>sum.code thresholdCircuitCodec

theorem witness_fields {limits : RecoveryWitnessLimits} (w : CheckedRecoveryWitness limits) (bits : List Bool)
    (h : value bits=w.code) :
    CompetitorWitnessTriple.field bits 3=encodeBooleanCircuit (witnessOracle w) ∧
    CompetitorWitnessTriple.field bits 5=witnessSumCode w ∧
    (CompetitorWitnessTriple.field bits 1=0 ↔ w.mode=.symmetric) := by
  cases w with
  | symmetric oracle hs sum=>
    obtain ⟨_,hm,ho,hsum⟩ := CompetitorWitnessTriple.extracted_values bits _ _ _ h
    refine ⟨ho,hsum,?_⟩
    rw [hm,CompetitorWitnessTriple.encoded_modes.1]
    simp [CheckedRecoveryWitness.mode]
  | threshold oracle hs sum=>
    obtain ⟨_,hm,ho,hsum⟩ := CompetitorWitnessTriple.extracted_values bits _ _ _ h
    refine ⟨ho,hsum,?_⟩
    rw [hm,CompetitorWitnessTriple.encoded_modes.2]
    simp [CheckedRecoveryWitness.mode]

theorem field_word (bits : List Bool) (k : ℕ) :
    RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits k)=
      SignedSortKey.binary bits.length (CompetitorWitnessTriple.field bits k) := by
  unfold RecoveryFixedUnpair.leftWord
  rw [CompetitorWitnessTriple.word_length]
  congr 1
  exact (RecoveryFixedUnpair.word_values (CompetitorWitnessTriple.word bits k)).1.symm

theorem checked_run {limits : RecoveryWitnessLimits} (w : CheckedRecoveryWitness limits)
    (x bits : List Bool) (h : value bits=w.code) :
    ∃ r : ExecutionReceipt 148 _,run machine (budget bits) (input x bits)=some r ∧
      r.steps ≤ budget bits ∧ (∀ i,r.final.heads i=0) ∧ readTapeBit (r.final.tapes 147) 0=true ∧
      r.final.tapes 78=frame (SignedSortKey.binary bits.length (encodeBooleanCircuit (witnessOracle w))) ∧
      r.final.tapes 118=frame (SignedSortKey.binary bits.length (witnessSumCode w)) ∧
      (readTapeBit (r.final.tapes 142) 0=true ↔ w.mode=.symmetric) := by
  obtain ⟨r,hr,hs,hh,ht⟩ := header_output x bits
  obtain ⟨ho,hsum,hmode⟩ := witness_fields w bits h
  refine ⟨r,hr,hs,hh,?_,?_,?_,?_⟩
  · rw [ht]
    exact (output_passes x bits).mpr (CompetitorWitnessTriple.checked_header w bits h)
  · rw [ht,output_oracle,field_word,ho]
  · rw [ht,output_sum,field_word,hsum]
  · rw [ht,output_family]
    change decide (CompetitorWitnessTriple.field bits 1=0)=true ↔_
    simpa only [decide_eq_true_eq] using hmode

end NearCubicWires.RepairOrdinary.CompetitorWitnessHeader

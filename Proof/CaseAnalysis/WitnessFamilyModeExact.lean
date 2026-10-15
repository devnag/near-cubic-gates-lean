import Proof.CaseAnalysis.CloseoutWitnessFamilyExact
import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun

/-! Both actual mode flags decide the original typed family decoder.
The internal circuit adapter is discharged by the executed SYM/THR flags. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode
open CanonicalWitnessCodec RadixSemantics CloseoutRowsCircuitTermSupplier RepairRepresentation SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem symmetric_flag_exact (core W L : ℕ) (bits : List Bool) :
    symmetricFlag core W L bits=true ↔ ∃ c,
      symmetricCircuitCodec.decode core (value (TermCoefficient.circuitCode bits))=some c ∧
        c.wireCount ≤ W ∧ c.descriptionBits ≤ L := by
  cases hd:decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits)) <;>
    simp [symmetricFlag,symmetricCircuitCodec,hd]

theorem threshold_flag_exact (core W L : ℕ) (bits : List Bool) :
    thresholdFlag core W L bits=true ↔ ∃ c,
      thresholdCircuitCodec.decode core (value (TermCoefficient.circuitCode bits))=some c ∧
        c.wireCount ≤ W ∧ c.descriptionBits ≤ L := by
  cases hd:decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits)) <;>
    simp [thresholdFlag,thresholdCircuitCodec,hd]

theorem symmetric_exact (limits : LegalSumLimits) (C V : ℕ) (bits arity : List Bool)
    (hC:limits.coefficientBitCap=natBitLength C)
    (ha:value arity=limits.expectedArity) (hb:1 ≤ limits.coefficientBitCap) :
    FamilyCold.passed true V C limits.termCap limits.expectedArity limits.wireCap
      limits.descriptionCap limits.coefficientMassCap bits arity=true ↔
      ∃ family,SumFamily.decode symmetricCircuitCodec
        NormalizedSymmetricThresholdCircuit.wireCount NormalizedSymmetricThresholdCircuit.descriptionBits
        limits V (value bits)=some family :=
  FamilyExact.passed_iff_decoded symmetricCircuitCodec
    NormalizedSymmetricThresholdCircuit.wireCount NormalizedSymmetricThresholdCircuit.descriptionBits
    limits C hC (symmetricFlag limits.expectedArity limits.wireCap limits.descriptionCap)
    (symmetric_flag_exact _ _ _) V bits arity ha hb

theorem threshold_exact (limits : LegalSumLimits) (C V : ℕ) (bits arity : List Bool)
    (hC:limits.coefficientBitCap=natBitLength C)
    (ha:value arity=limits.expectedArity) (hb:1 ≤ limits.coefficientBitCap) :
    FamilyCold.passed false V C limits.termCap limits.expectedArity limits.wireCap
      limits.descriptionCap limits.coefficientMassCap bits arity=true ↔
      ∃ family,SumFamily.decode thresholdCircuitCodec
        NormalizedThresholdThresholdCircuit.wireCount NormalizedThresholdThresholdCircuit.descriptionBits
        limits V (value bits)=some family :=
  FamilyExact.passed_iff_decoded thresholdCircuitCodec
    NormalizedThresholdThresholdCircuit.wireCount NormalizedThresholdThresholdCircuit.descriptionBits
    limits C hC (thresholdFlag limits.expectedArity limits.wireCap limits.descriptionCap)
    (threshold_flag_exact _ _ _) V bits arity ha hb

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode

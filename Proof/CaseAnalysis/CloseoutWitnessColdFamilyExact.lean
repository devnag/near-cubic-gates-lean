import Proof.CaseAnalysis.WitnessFamilyModeExact
import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! The executed source-dependent family policy is exactly the original
sampled-witness policy, including its actual clause count and mode caps. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open SourceInterfaces RepairSource RepairRepresentation CanonicalWitnessCodec SupplierPipeline RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
variable (a : PointwisePCPPAlgorithm) (k CH Cpad D copies e den : ℕ) (delta : ℚ)
variable (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad:k+3≤Cpad)
variable (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))

theorem familyFlag_symmetric_exact :
    familyFlag source a k CH Cpad D copies e den delta code true x bits hpad oracle=true ↔
      let r:=ColdNative.request source a k CH Cpad code x hpad oracle
      ∃ family,SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.symmetricLimits a r (CloseoutLanguage.clauseWidth D r.arity)
          copies (LegalPolicy.W e den r.arity) delta)
        ((a.output r).systematicBits+(a.output r).auxiliaryBits) (value bits)=some family := by
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let limits:=CloseoutSampledWitness.symmetricLimits a r (CloseoutLanguage.clauseWidth D r.arity)
    copies (LegalPolicy.W e den r.arity) delta
  exact FamilyMode.symmetric_exact limits
    (FamilyResources.coefficientCap delta copies D r.arity (a.output r).clauseBits) _ bits _ rfl
    (SignedSortKey.binary_value _ _ (Nat.lt_pow_succ_log_self Nat.one_lt_two _))
    (by dsimp only [limits,CloseoutSampledWitness.symmetricLimits,Average.limits,natBitLength];omega)

theorem familyFlag_threshold_exact :
    familyFlag source a k CH Cpad D copies e den delta code false x bits hpad oracle=true ↔
      let r:=ColdNative.request source a k CH Cpad code x hpad oracle
      ∃ family,SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.thresholdLimits a r (CloseoutLanguage.clauseWidth D r.arity)
          copies (LegalPolicy.W e den r.arity) delta)
        ((a.output r).systematicBits+(a.output r).auxiliaryBits) (value bits)=some family := by
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let limits:=CloseoutSampledWitness.thresholdLimits a r (CloseoutLanguage.clauseWidth D r.arity)
    copies (LegalPolicy.W e den r.arity) delta
  exact FamilyMode.threshold_exact limits
    (FamilyResources.coefficientCap delta copies D r.arity (a.output r).clauseBits) _ bits _ rfl
    (SignedSortKey.binary_value _ _ (Nat.lt_pow_succ_log_self Nat.one_lt_two _))
    (by dsimp only [limits,CloseoutSampledWitness.thresholdLimits,Average.limits,natBitLength];omega)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily

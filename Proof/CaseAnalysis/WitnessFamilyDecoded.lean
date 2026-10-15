import Proof.CaseAnalysis.CloseoutWitnessColdFamilyExact

/-! A compact semantic projection of the same cold verdict. This only
names existence in the original typed decoders; it adds no parser or source. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open SourceInterfaces RepairSource RepairRepresentation CanonicalWitnessCodec SupplierPipeline RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
variable (a : PointwisePCPPAlgorithm) (k CH Cpad D copies e den : ℕ) (delta : ℚ)
variable (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad:k+3≤Cpad)

def decodedFamily
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))) : Prop :=
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let R:=CloseoutLanguage.clauseWidth D r.arity
  let W:=LegalPolicy.W e den r.arity
  let V:=(a.output r).systematicBits+(a.output r).auxiliaryBits
  if sym then ∃ family,SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
    NormalizedSymmetricThresholdCircuit.descriptionBits
    (CloseoutSampledWitness.symmetricLimits a r R copies W delta) V (value bits)=some family
  else ∃ family,SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
    NormalizedThresholdThresholdCircuit.descriptionBits
    (CloseoutSampledWitness.thresholdLimits a r R copies W delta) V (value bits)=some family

theorem familyFlag_exact
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))) :
    familyFlag source a k CH Cpad D copies e den delta code sym x bits hpad oracle=true ↔
      decodedFamily source a k CH Cpad D copies e den delta code sym x bits hpad oracle := by
  cases sym
  · exact familyFlag_threshold_exact source a k CH Cpad D copies e den delta code x bits hpad oracle
  · exact familyFlag_symmetric_exact source a k CH Cpad D copies e den delta code x bits hpad oracle

theorem passed_exact (cutoff G : ℕ) (raw : List Bool) :
    passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=true ↔
      ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true ∧
        ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
          (value raw)=some oracle ∧
          decodedFamily source a k CH Cpad D copies e den delta code sym x bits hpad oracle := by
  rw [passed,Bool.and_eq_true]
  apply and_congr_right
  intro _
  cases hd:decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw) with
  | none=>simp
  | some oracle=>
    simp only [Option.any_some,Option.some.injEq]
    constructor
    · intro h
      exact ⟨oracle,rfl,(familyFlag_exact source a k CH Cpad D copies e den delta code sym x bits hpad oracle).mp h⟩
    · rintro ⟨other,eq,h⟩
      subst other
      exact (familyFlag_exact source a k CH Cpad D copies e den delta code sym x bits hpad oracle).mpr h

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily

import Proof.CaseAnalysis.WitnessHonest
import Proof.CaseAnalysis.SourceTermMeaning
import Proof.CaseAnalysis.Xor
import Proof.CaseAnalysis.Language

/-! Direct binding of the unchanged XOR source sample to the actual honest
family. All numeric, mass, normalization and occurrence premises are paid
here; no stronger arbitrary-sum farness statement is introduced. -/
namespace NearCubicWires.RepairSource.CloseoutSampledWitness
open SourceInterfaces RepairRepresentation RepairOrdinary CanonicalWitnessCodec
open CloseoutWitness ComponentwiseCircuitRestriction RecoveryWitnessPolicy
open SupplierPipeline CircuitRestriction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def massCap (delta : ℚ) (copies : Nat) : ℚ := 1/epsilonQ delta copies
theorem mass_nonneg (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2) (copies : Nat) :
    0 ≤ massCap delta copies := by
  have hhr : (delta : ℝ)<((1/2 : ℚ) : ℝ) := Rat.cast_lt.mpr hh
  norm_num at hhr
  have he:=RepairXor.epsilon_positive (delta : ℝ) (by exact_mod_cast hd) hhr copies
  have hc : (massCap delta copies : ℝ)=1/xorEpsilon (delta : ℝ) copies := by
    simp [massCap,RepairXor.epsilonQ_coe]
  have h : (0 : ℝ) ≤ (massCap delta copies : ℝ) := by rw [hc];positivity
  exact_mod_cast h

theorem resources {Circuit : CanonicalWitnessCodec.CircuitFamily} {family : SizedFunctionFamily}
    {n size copies : Nat} (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2) (hn : 1 ≤ n)
    (evaluate : Circuit n→BoolFunction n) (terms : List (LegalCircuitTerm Circuit n))
    (sum : UnitIntervalCircuitSum family n size)
    (meaning : terms.map (fun t=>(t.coefficient,evaluate t.circuit))=sum.terms)
    (form : SampleForm delta n copies sum.terms) :
    terms.length ≤ xorTermBound delta n copies ∧ Average.mass terms ≤ massCap delta copies ∧
    (∀ t∈terms,t.coefficient.num.natAbs ≤ CloseoutXor.cap delta n copies ∧
      t.coefficient.den ≤ CloseoutXor.cap delta n copies) ∧
    (∀ x,0 ≤ Average.value evaluate terms x) ∧ (∀ x,Average.value evaluate terms x ≤ 1) := by
  obtain ⟨hj,_,hm⟩:=RepairXor.sampleForm_resources delta hd hh hn sum.terms form
  have hv (x : BitInput n) : Average.value evaluate terms x=sum.value x :=
    CloseoutSourceTerms.value evaluate terms sum meaning x
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [CloseoutSourceTerms.term_count evaluate terms sum meaning]
    exact hj
  · have he : (Average.mass terms : ℝ)=sum.coefficientMass :=
      CloseoutSourceTerms.mass evaluate terms sum meaning
    have hc : (massCap delta copies : ℝ)=1/xorEpsilon (delta : ℝ) copies := by
      simp [massCap,RepairXor.epsilonQ_coe]
    exact_mod_cast (show (Average.mass terms : ℝ) ≤ (massCap delta copies : ℝ) by rw [he,hc];exact hm)
  · intro t ht
    exact CloseoutXor.sampleForm_magnitudes delta hd hh sum.terms form _
      (CloseoutSourceTerms.term_member evaluate terms sum meaning t ht)
  · intro x;rw [hv];exact (sum.inUnitInterval x).1
  · intro x;rw [hv];exact (sum.inUnitInterval x).2

def symmetricLimits (source : PointwisePCPPAlgorithm) (request : PCPPRequest source.minimumArity)
    (r copies wireCap : Nat) (delta : ℚ) :=
  let n:=request.arity+r+1
  Average.limits request.arity (xorTermBound delta n copies) (CloseoutXor.cap delta n copies)
    (2*2^(source.output request).clauseBits) (massCap delta copies) wireCap
    (restrictedSymmetricDescriptionCap request.arity n (2^symmetricDescriptionCap n wireCap) wireCap)
def thresholdLimits (source : PointwisePCPPAlgorithm) (request : PCPPRequest source.minimumArity)
    (r copies wireCap : Nat) (delta : ℚ) :=
  let n:=request.arity+r+1
  Average.limits request.arity (xorTermBound delta n copies) (CloseoutXor.cap delta n copies)
    (2*2^(source.output request).clauseBits) (massCap delta copies) wireCap
    (restrictedThresholdDescriptionCap request.arity n (2^thresholdDescriptionCap n wireCap)
      (thresholdDescriptionCap n wireCap))

theorem symmetric_family (normalization : ThresholdNormalizationContract)
    (source : PointwisePCPPAlgorithm) (request : PCPPRequest source.minimumArity)
    (r copies wireCap : Nat) (hr : (source.output request).clauseBits ≤ r)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (sample : SampledXorSum symmetricWireFamily delta (request.arity+r+1) copies wireCap
      (CloseoutLanguage.paddedUnsigned (source.output request) hr)) :
    ∃ family : SumFamily NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount NormalizedSymmetricThresholdCircuit.descriptionBits
      (symmetricLimits source request r copies wireCap delta)
      ((source.output request).systematicBits+(source.output request).auxiliaryBits),
      CompetitorSourceAverage.honestError source request (family.value NormalizedSymmetricThresholdCircuit.eval) ≤
        (delta : ℝ) ∧ ∀ u i,0 ≤ family.value NormalizedSymmetricThresholdCircuit.eval u i ∧
          family.value NormalizedSymmetricThresholdCircuit.eval u i ≤ 1 := by
  obtain ⟨terms,meaning,hbounds⟩:=CloseoutSourceTerms.symmetric_terms normalization sample.sum
  obtain ⟨hj,hm,hc,h0,h1⟩:=resources delta hd hh (by omega)
    NormalizedSymmetricThresholdCircuit.eval terms sample.sum meaning sample.form
  obtain ⟨family,he,hu⟩:=Honest.symmetric_family source request r hr terms _ _ _ _ _
    (mass_nonneg delta hd hh copies) hj hm hc (fun t ht=>(hbounds t ht).1)
    (fun t ht=>(hbounds t ht).2) h0 h1
  have hv : Average.value NormalizedSymmetricThresholdCircuit.eval terms=sample.sum.value :=
    funext (CloseoutSourceTerms.value _ _ _ meaning)
  rw [hv] at he
  exact ⟨family,he.trans sample.close,hu⟩

theorem threshold_family (normalization : ThresholdNormalizationContract)
    (source : PointwisePCPPAlgorithm) (request : PCPPRequest source.minimumArity)
    (r copies wireCap : Nat) (hr : (source.output request).clauseBits ≤ r)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (sample : SampledXorSum thresholdWireFamily delta (request.arity+r+1) copies wireCap
      (CloseoutLanguage.paddedUnsigned (source.output request) hr)) :
    ∃ family : SumFamily NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount NormalizedThresholdThresholdCircuit.descriptionBits
      (thresholdLimits source request r copies wireCap delta)
      ((source.output request).systematicBits+(source.output request).auxiliaryBits),
      CompetitorSourceAverage.honestError source request (family.value NormalizedThresholdThresholdCircuit.eval) ≤
        (delta : ℝ) ∧ ∀ u i,0 ≤ family.value NormalizedThresholdThresholdCircuit.eval u i ∧
          family.value NormalizedThresholdThresholdCircuit.eval u i ≤ 1 := by
  obtain ⟨terms,meaning,hbounds⟩:=CloseoutSourceTerms.threshold_terms normalization sample.sum
  obtain ⟨hj,hm,hc,h0,h1⟩:=resources delta hd hh (by omega)
    NormalizedThresholdThresholdCircuit.eval terms sample.sum meaning sample.form
  obtain ⟨family,he,hu⟩:=Honest.threshold_family source request r hr terms _ _ _ _ _
    (mass_nonneg delta hd hh copies) hj hm hc (fun t ht=>(hbounds t ht).1)
    (fun t ht=>(hbounds t ht).2) h0 h1
  have hv : Average.value NormalizedThresholdThresholdCircuit.eval terms=sample.sum.value :=
    funext (CloseoutSourceTerms.value _ _ _ meaning)
  rw [hv] at he
  exact ⟨family,he.trans sample.close,hu⟩

end
end NearCubicWires.RepairSource.CloseoutSampledWitness

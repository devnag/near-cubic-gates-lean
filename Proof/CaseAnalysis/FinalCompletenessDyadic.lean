import Proof.CaseAnalysis.FinalObligations
import Proof.CaseAnalysis.SampledWitness

/-! Paper C.10 honest completeness, at the consumer, dyadic only.

`hardness_pair` needs sampled completeness only at lengths `2^s` after one
onset -- never all-`N`, and never a pre-averaged `CircuitSum` statement. The
sampling half is already accepted: `CloseoutSampledWitness.symmetric_family`
and `threshold_family` turn a `SampledXorSum` into an honest real proof family
with average `l_1` error at most `delta`, unit-valued, at the SAME source
request, closing normalization, the sharp coefficient, averaging and range.

This module removes that half from the obligation. What is left for the
producer is exactly: encode an honest unit-valued family of small error as a
witness string on which the machine's acceptance predicate holds. That is the
`Encodes` hypothesis below, and it is the only completeness content the
physical stack still owes. -/
namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairRepresentation SourceInterfaces SupplierPipeline
open SelectedRecoveryIntegration CloseoutLanguage CircuitRestriction
open RepairOrdinary.CloseoutWitness

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))

/-- The producer obligation: an honest, unit-valued real proof family whose
average distance from a Boolean proof is at most `delta` is encodable as a
witness string the machine accepts. Stated at the selected request, for the
symmetric class. -/
def EncodesSym (meaning : (n : Nat) → BitInput n → List Bool → Prop)
    (degree copies clauseDegree : Nat) (delta : ℚ) (cap : ℝ) (onset : Nat) : Prop :=
  ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
    ∀ hsmall : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input,
    let oracle := (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
    let request := CloseoutWitnessPolicy.request sources k clock input oracle
    let pcpp := (selectedPCPP sources).output request
    let cb := clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s))
    ∀ _hc : pcpp.clauseBits ≤ cb,
    ∀ family : CloseoutWitness.SumFamily NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources) request cb copies
          (Nat.floor (wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s)))) delta)
        (pcpp.systematicBits + pcpp.auxiliaryBits),
      CompetitorSourceAverage.honestError (selectedPCPP sources) request
        (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family) ≤ (delta : ℝ) →
      (∀ u i, 0 ≤ CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family u i ∧
        CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family u i ≤ 1) →
      ∃ w : BitInput (2^s/16), meaning (2^s) input (List.ofFn w)

/-- Sampled completeness at the symmetric family follows from the encoder
obligation alone: `symmetric_family` supplies the honest family, its error
bound and its unit range from the `SampledXorSum`. Nothing else about sampling,
normalization or averaging remains. -/
theorem completeness_of_encodesSym
    (meaning : (n : Nat) → BitInput n → List Bool → Prop)
    (degree copies clauseDegree : Nat) (delta : ℚ) (cap : ℝ) (onset : Nat)
    (hd : 0 < delta) (hh : delta < 1/2)
    (h : EncodesSym sources k clock meaning degree copies clauseDegree delta cap onset) :
    Completeness sources k clock meaning degree copies clauseDegree delta
      symmetricWireFamily 5 cap := by
  refine ⟨onset, ?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb hc sample
  obtain ⟨family, herr, hunit⟩ :=
    CloseoutSampledWitness.symmetric_family sources.normalization (selectedPCPP sources)
      (CloseoutWitnessPolicy.request sources k clock input
        (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit)
      (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
      copies (Nat.floor (wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))))
      hc delta hd hh sample
  exact h s hs input hsmall hc family herr hunit

/-- The producer obligation: an honest, unit-valued real proof family whose
average distance from a Boolean proof is at most `delta` is encodable as a
witness string the machine accepts. Stated at the selected request, for the
threshold class. -/
def EncodesThr (meaning : (n : Nat) → BitInput n → List Bool → Prop)
    (degree copies clauseDegree : Nat) (delta : ℚ) (cap : ℝ) (onset : Nat) : Prop :=
  ∀ s, onset ≤ s → ∀ input : BitInput (2^s),
    ∀ hsmall : RecoveryChoice.SmallOracle (outer sources k clock).result.pcp degree input,
    let oracle := (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
    let request := CloseoutWitnessPolicy.request sources k clock input oracle
    let pcpp := (selectedPCPP sources).output request
    let cb := clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s))
    ∀ _hc : pcpp.clauseBits ≤ cb,
    ∀ family : CloseoutWitness.SumFamily NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources) request cb copies
          (Nat.floor (wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s)))) delta)
        (pcpp.systematicBits + pcpp.auxiliaryBits),
      CompetitorSourceAverage.honestError (selectedPCPP sources) request
        (CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family) ≤ (delta : ℝ) →
      (∀ u i, 0 ≤ CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family u i ∧
        CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family u i ≤ 1) →
      ∃ w : BitInput (2^s/16), meaning (2^s) input (List.ofFn w)

/-- Sampled completeness at the symmetric family follows from the encoder
obligation alone: `threshold_family` supplies the honest family, its error
bound and its unit range from the `SampledXorSum`. Nothing else about sampling,
normalization or averaging remains. -/
theorem completeness_of_encodesThr
    (meaning : (n : Nat) → BitInput n → List Bool → Prop)
    (degree copies clauseDegree : Nat) (delta : ℚ) (cap : ℝ) (onset : Nat)
    (hd : 0 < delta) (hh : delta < 1/2)
    (h : EncodesThr sources k clock meaning degree copies clauseDegree delta cap onset) :
    Completeness sources k clock meaning degree copies clauseDegree delta
      thresholdWireFamily 9 cap := by
  refine ⟨onset, ?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb hc sample
  obtain ⟨family, herr, hunit⟩ :=
    CloseoutSampledWitness.threshold_family sources.normalization (selectedPCPP sources)
      (CloseoutWitnessPolicy.request sources k clock input
        (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit)
      (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
      copies (Nat.floor (wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))))
      hc delta hd hh sample
  exact h s hs input hsmall hc family herr hunit

end
end NearCubicWires.RepairSource.CloseoutFinal

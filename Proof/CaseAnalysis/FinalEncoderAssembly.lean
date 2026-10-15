import Proof.CaseAnalysis.FinalEncoder
import Proof.CaseAnalysis.FinalSupplierTotality

namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The machine-side interface for the SYMMETRIC completeness leg.

Read: on a witness string whose header is valid, whose oracle field decodes to
`oracle`, whose payload decodes to `family` and whose mode bit says
"symmetric", the worker exposes three reals within `eps_est` of paper C.10's
three means for that family, and accepts whenever those three reals pass
paper C.10's validity tests and C.10.1's acceptance test.

This is W1 + P2 + P5 restricted to the completeness direction. -/
def SymDecides (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ) : Prop :=
  ∀ (s : Nat) (input : BitInput (2^s))
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)))
    (family : CloseoutWitness.SumFamily NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
        (CloseoutWitnessPolicy.request sources k clock input oracle)
        (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
        copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
      (CloseoutWitnessPolicy.variableCount sources k clock input oracle))
    (guess : BitInput (2^s/16)),
    16*(List.ofFn guess).length ≤ 2^s →
    CompetitorWitnessTriple.headerValid (List.ofFn guess) →
    decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s))
        (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle →
    CloseoutWitness.SumFamily.decode symmetricCircuitCodec
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
          (CloseoutWitnessPolicy.request sources k clock input oracle)
          (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
          copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
        (CloseoutWitnessPolicy.variableCount sources k clock input oracle)
        (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family →
    BoundedFields.symmetric (List.ofFn guess) = true →
    ∃ penaltyEstimate momentEstimate clauseEstimate : ℝ,
      |penaltyEstimate - aggregateClausePenaltyMean
          ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
          (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family)/2| ≤
        estimationTolerance constants (zeta constants) ∧
      |momentEstimate - leftSecondMoment
          ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
          (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family)| ≤
        estimationTolerance constants (zeta constants) ∧
      |clauseEstimate - aggregateClauseMean
          ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
          (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family)| ≤
        estimationTolerance constants (zeta constants) ∧
      (penaltyEstimate ≤ 2*(zeta constants : ℝ) → momentEstimate ≤ 1+(zeta constants : ℝ) →
        (midpoint constants : ℝ) < clauseEstimate →
        Weak.decides worker ht result fuel (2^s) input (List.ofFn guess))

/-- The same interface for the THRESHOLD completeness leg: exponent `9` in the
wire cap, `thresholdCircuitCodec` for the payload, a `false` mode bit. -/
def ThrDecides (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ) : Prop :=
  ∀ (s : Nat) (input : BitInput (2^s))
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)))
    (family : CloseoutWitness.SumFamily NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
        (CloseoutWitnessPolicy.request sources k clock input oracle)
        (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
        copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
      (CloseoutWitnessPolicy.variableCount sources k clock input oracle))
    (guess : BitInput (2^s/16)),
    16*(List.ofFn guess).length ≤ 2^s →
    CompetitorWitnessTriple.headerValid (List.ofFn guess) →
    decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s))
        (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle →
    CloseoutWitness.SumFamily.decode thresholdCircuitCodec
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
          (CloseoutWitnessPolicy.request sources k clock input oracle)
          (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
          copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
        (CloseoutWitnessPolicy.variableCount sources k clock input oracle)
        (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family →
    BoundedFields.symmetric (List.ofFn guess) = false →
    ∃ penaltyEstimate momentEstimate clauseEstimate : ℝ,
      |penaltyEstimate - aggregateClausePenaltyMean
          ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
          (CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family)/2| ≤
        estimationTolerance constants (zeta constants) ∧
      |momentEstimate - leftSecondMoment
          ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
          (CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family)| ≤
        estimationTolerance constants (zeta constants) ∧
      |clauseEstimate - aggregateClauseMean
          ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
          (CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family)| ≤
        estimationTolerance constants (zeta constants) ∧
      (penaltyEstimate ≤ 2*(zeta constants : ℝ) → momentEstimate ≤ 1+(zeta constants : ℝ) →
        (midpoint constants : ℝ) < clauseEstimate →
        Weak.decides worker ht result fuel (2^s) input (List.ofFn guess))

/-- **E1, symmetric.** The completeness obligation of `PhysicalWitness`, from
the machine-side interface alone. `hyes` is supplied internally by
`selected_request_true`; `hzeta` is `delta <= zeta constants`. -/
theorem encodesSym_of_symDecides (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (degree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (hzeta : (delta : ℝ) ≤ (zeta constants : ℝ))
    (hdec : SymDecides sources k clock constants worker ht result fuel clauseDegree copies delta cap) :
    ∃ onset, EncodesSym sources k clock
      (Weak.decides worker ht result fuel)
      degree copies clauseDegree delta cap onset := by
  obtain ⟨onset, hguess⟩ :=
    symmetric_family_guess sources k clock degree clauseDegree copies delta cap
  refine ⟨onset, ?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb _hc family herr hunit
  obtain ⟨guess, hlen, hheader, horacle, hpayload, hmode⟩ :=
    hguess s hs input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      (selected_oracle_small sources k clock degree input hsmall) family
  obtain ⟨penaltyEstimate, momentEstimate, clauseEstimate, hp, hm, hcl, hacc⟩ :=
    hdec s input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      family guess hlen hheader horacle hpayload hmode
  obtain ⟨hvalidity, hmoment, hthreshold⟩ :=
    honest_estimates_pass (selectedPCPP sources) constants
      (CloseoutWitnessPolicy.request sources k clock input
        (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit)
      (selected_yes sources k clock degree input hsmall)
      (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family)
      (fun u i => (hunit u i).1) (fun u i => (hunit u i).2) (herr.trans hzeta)
      penaltyEstimate momentEstimate clauseEstimate hp hm hcl
  exact ⟨guess, hacc hvalidity hmoment hthreshold⟩

/-- **E1, threshold.** The same, for the threshold class. -/
theorem encodesThr_of_thrDecides (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (degree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (hzeta : (delta : ℝ) ≤ (zeta constants : ℝ))
    (hdec : ThrDecides sources k clock constants worker ht result fuel clauseDegree copies delta cap) :
    ∃ onset, EncodesThr sources k clock
      (Weak.decides worker ht result fuel)
      degree copies clauseDegree delta cap onset := by
  obtain ⟨onset, hguess⟩ :=
    threshold_family_guess sources k clock degree clauseDegree copies delta cap
  refine ⟨onset, ?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb _hc family herr hunit
  obtain ⟨guess, hlen, hheader, horacle, hpayload, hmode⟩ :=
    hguess s hs input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      (selected_oracle_small sources k clock degree input hsmall) family
  obtain ⟨penaltyEstimate, momentEstimate, clauseEstimate, hp, hm, hcl, hacc⟩ :=
    hdec s input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      family guess hlen hheader horacle hpayload hmode
  obtain ⟨hvalidity, hmoment, hthreshold⟩ :=
    honest_estimates_pass (selectedPCPP sources) constants
      (CloseoutWitnessPolicy.request sources k clock input
        (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit)
      (selected_yes sources k clock degree input hsmall)
      (CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family)
      (fun u i => (hunit u i).1) (fun u i => (hunit u i).2) (herr.trans hzeta)
      penaltyEstimate momentEstimate clauseEstimate hp hm hcl
  exact ⟨guess, hacc hvalidity hmoment hthreshold⟩

end
end NearCubicWires.RepairSource.CloseoutFinal

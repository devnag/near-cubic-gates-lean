import Proof.CaseAnalysis.FinalEncoderAssembly

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

def SymDecidesFrom (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (oracleDegree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (onset : Nat) : Prop :=
  ∀ (s : Nat), onset ≤ s → ∀ (input : BitInput (2^s))
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
    oracle.size ≤ oracleSizeBound oracleDegree
        ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
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

def ThrDecidesFrom (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (oracleDegree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (onset : Nat) : Prop :=
  ∀ (s : Nat), onset ≤ s → ∀ (input : BitInput (2^s))
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
    oracle.size ≤ oracleSizeBound oracleDegree
        ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
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

/-- **E1, symmetric, onset-indexed.** Identical to `encodesSym_of_symDecides`
except that `hdec` is only ever used above `max` of the two onsets. -/
theorem encodesSym_of_symDecidesFrom (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (degree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (gateOnset : Nat) (hzeta : (delta : ℝ) ≤ (zeta constants : ℝ))
    (hdec : SymDecidesFrom sources k clock constants worker ht result fuel
      degree clauseDegree copies delta cap gateOnset) :
    ∃ onset, EncodesSym sources k clock
      (Weak.decides worker ht result fuel)
      degree copies clauseDegree delta cap onset := by
  obtain ⟨onset, hguess⟩ :=
    symmetric_family_guess sources k clock degree clauseDegree copies delta cap
  refine ⟨max gateOnset onset, ?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb _hc family herr hunit
  have hs0 : gateOnset ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : onset ≤ s := le_trans (le_max_right _ _) hs
  obtain ⟨guess, hlen, hheader, horacle, hpayload, hmode⟩ :=
    hguess s hs1 input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      (selected_oracle_small sources k clock degree input hsmall) family
  obtain ⟨penaltyEstimate, momentEstimate, clauseEstimate, hp, hm, hcl, hacc⟩ :=
    hdec s hs0 input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      family guess hlen hheader horacle
      (selected_oracle_small sources k clock degree input hsmall) hpayload hmode
  obtain ⟨hvalidity, hmoment, hthreshold⟩ :=
    honest_estimates_pass (selectedPCPP sources) constants
      (CloseoutWitnessPolicy.request sources k clock input
        (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit)
      (selected_yes sources k clock degree input hsmall)
      (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family)
      (fun u i => (hunit u i).1) (fun u i => (hunit u i).2) (herr.trans hzeta)
      penaltyEstimate momentEstimate clauseEstimate hp hm hcl
  exact ⟨guess, hacc hvalidity hmoment hthreshold⟩

/-- **E1, threshold, onset-indexed.** -/
theorem encodesThr_of_thrDecidesFrom (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (degree clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (gateOnset : Nat) (hzeta : (delta : ℝ) ≤ (zeta constants : ℝ))
    (hdec : ThrDecidesFrom sources k clock constants worker ht result fuel
      degree clauseDegree copies delta cap gateOnset) :
    ∃ onset, EncodesThr sources k clock
      (Weak.decides worker ht result fuel)
      degree copies clauseDegree delta cap onset := by
  obtain ⟨onset, hguess⟩ :=
    threshold_family_guess sources k clock degree clauseDegree copies delta cap
  refine ⟨max gateOnset onset, ?_⟩
  intro s hs input hsmall _oracle _request _pcpp _cb _hc family herr hunit
  have hs0 : gateOnset ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : onset ≤ s := le_trans (le_max_right _ _) hs
  obtain ⟨guess, hlen, hheader, horacle, hpayload, hmode⟩ :=
    hguess s hs1 input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      (selected_oracle_small sources k clock degree input hsmall) family
  obtain ⟨penaltyEstimate, momentEstimate, clauseEstimate, hp, hm, hcl, hacc⟩ :=
    hdec s hs0 input
      (RecoveryChoice.oracleSelector (outer sources k clock).result.pcp degree input hsmall).circuit
      family guess hlen hheader horacle
      (selected_oracle_small sources k clock degree input hsmall) hpayload hmode
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

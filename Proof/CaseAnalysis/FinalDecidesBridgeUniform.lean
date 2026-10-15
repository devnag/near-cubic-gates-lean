import Proof.CaseAnalysis.FinalTotalDecode
import Proof.CaseAnalysis.FinalDecidesBridge

namespace NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CloseoutFinal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))

def PinnedSym' (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (s : Nat) (input : BitInput (2^s))
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)))
    (family : CloseoutWitness.SumFamily NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
        (CloseoutWitnessPolicy.request sources k clock input oracle)
        (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
        copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
      (CloseoutWitnessPolicy.variableCount sources k clock input oracle))
    (guess : BitInput (2^s/16)) : Type 1 :=
  Σ' (_Atom : Type)
     (evaluate : _Atom →
       BitInput (CloseoutWitnessPolicy.request sources k clock input oracle).arity → Bool)
     (ports : CloseoutRowsOriginalSchedule.Phase → Fin t)
     (width : CloseoutRowsOriginalSchedule.Phase → Nat),
    Verdict constants
      ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
      (CloseoutWitness.SumFamily.value NormalizedSymmetricThresholdCircuit.eval family)
      evaluate worker ht fuel (2^s) input (List.ofFn guess) result ports width

/-- **T3's obligation at a threshold guess.** Same shape with the threshold family. -/
def PinnedThr' (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (clauseDegree copies : Nat) (delta : ℚ) (cap : ℝ)
    (s : Nat) (input : BitInput (2^s))
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)))
    (family : CloseoutWitness.SumFamily NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
        (CloseoutWitnessPolicy.request sources k clock input oracle)
        (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
        copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
      (CloseoutWitnessPolicy.variableCount sources k clock input oracle))
    (guess : BitInput (2^s/16)) : Type 1 :=
  Σ' (_Atom : Type)
     (evaluate : _Atom →
       BitInput (CloseoutWitnessPolicy.request sources k clock input oracle).arity → Bool)
     (ports : CloseoutRowsOriginalSchedule.Phase → Fin t)
     (width : CloseoutRowsOriginalSchedule.Phase → Nat),
    Verdict constants
      ((selectedPCPP sources).output (CloseoutWitnessPolicy.request sources k clock input oracle))
      (CloseoutWitness.SumFamily.value NormalizedThresholdThresholdCircuit.eval family)
      evaluate worker ht fuel (2^s) input (List.ofFn guess) result ports width

theorem symDecides_of_pinned' (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (oracleDegree clauseDegree copies : Nat) (cap : ℝ) (gateOnset : Nat)
    (hcut : ∀ s, gateOnset ≤ s → Soundness.cutoff constants ≤ 2^s)
    (pinned : ∀ (s : Nat), gateOnset ≤ s → ∀ (input : BitInput (2^s))
      (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)))
      (family : CloseoutWitness.SumFamily NormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
          (CloseoutWitnessPolicy.request sources k clock input oracle)
          (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
          copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊
          (zeta constants))
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
            copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊
            (zeta constants))
          (CloseoutWitnessPolicy.variableCount sources k clock input oracle)
          (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family →
      BoundedFields.symmetric (List.ofFn guess) = true →
      PinnedSym' sources k clock constants worker ht result fuel clauseDegree copies
        (zeta constants) cap s input oracle family guess) :
    SymDecidesFrom sources k clock constants worker ht result fuel oracleDegree clauseDegree copies
      (zeta constants) cap gateOnset := by
  intro s hs input oracle family guess hlen hheader horacle hsize hfamily hmode
  obtain ⟨_Atom, _evaluate, _ports, _width, V⟩ :=
    pinned s hs input oracle family guess hlen hheader horacle hsize hfamily hmode
  have hc : Soundness.cutoff constants ≤ 2^s := hcut s hs
  refine ⟨V.estimate .penalty, V.estimate .moment, V.estimate .clause, ?_, ?_, ?_, ?_⟩
  · have h := accurate_of_verdict V hc .penalty
    rwa [penalty_mean] at h
  · have h := accurate_of_verdict V hc .moment
    rwa [moment_mean] at h
  · have h := accurate_of_verdict V hc .clause
    rwa [clause_mean] at h
  · intro hp hm hcl
    exact C10Decides.decides_of_verdict sources V (accepts_of_thresholds V hc hp hm (le_of_lt hcl))

/-- **`c10.machine.thrDecides` from pinned verdicts.** Same proof, threshold family. -/
theorem thrDecides_of_pinned' (constants : Constants (selectedPCPP sources))
    {t st : Nat} (worker : LocalBitMultitape.Machine t st) (ht : 2 ≤ t) (result : Fin t)
    (fuel : Nat → Nat) (oracleDegree clauseDegree copies : Nat) (cap : ℝ) (gateOnset : Nat)
    (hcut : ∀ s, gateOnset ≤ s → Soundness.cutoff constants ≤ 2^s)
    (pinned : ∀ (s : Nat), gateOnset ≤ s → ∀ (input : BitInput (2^s))
      (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)))
      (family : CloseoutWitness.SumFamily NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits
        (CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
          (CloseoutWitnessPolicy.request sources k clock input oracle)
          (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
          copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊
          (zeta constants))
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
            copies ⌊wireScale cap 9 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊
            (zeta constants))
          (CloseoutWitnessPolicy.variableCount sources k clock input oracle)
          (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family →
      BoundedFields.symmetric (List.ofFn guess) = false →
      PinnedThr' sources k clock constants worker ht result fuel clauseDegree copies
        (zeta constants) cap s input oracle family guess) :
    ThrDecidesFrom sources k clock constants worker ht result fuel oracleDegree clauseDegree copies
      (zeta constants) cap gateOnset := by
  intro s hs input oracle family guess hlen hheader horacle hsize hfamily hmode
  obtain ⟨_Atom, _evaluate, _ports, _width, V⟩ :=
    pinned s hs input oracle family guess hlen hheader horacle hsize hfamily hmode
  have hc : Soundness.cutoff constants ≤ 2^s := hcut s hs
  refine ⟨V.estimate .penalty, V.estimate .moment, V.estimate .clause, ?_, ?_, ?_, ?_⟩
  · have h := accurate_of_verdict V hc .penalty
    rwa [penalty_mean] at h
  · have h := accurate_of_verdict V hc .moment
    rwa [moment_mean] at h
  · have h := accurate_of_verdict V hc .clause
    rwa [clause_mean] at h
  · intro hp hm hcl
    exact C10Decides.decides_of_verdict sources V (accepts_of_thresholds V hc hp hm (le_of_lt hcl))

end
end NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform

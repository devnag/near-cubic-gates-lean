import Proof.CaseAnalysis.FinalTotalDecode

namespace NearCubicWires.P1Independent.CappedDecode
open RepairSource RepairSource.CloseoutFinal
open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

open RepairSource RepairSource.CloseoutFinal RepairSource.CloseoutFinal.C10TotalDecode

variable (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2)))

variable {gamma : ℝ} (p : Parameters sources gamma) (den : ℕ)

abbrev symLimits {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
    (CloseoutWitnessPolicy.request sources k clock x oracle)
    (clauseWidth p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n))
    p.copies ⌊wireScale (1 / (den : ℝ)) 5 ((outer sources k clock).result.pcp.nativeWidth n)⌋₊
    (zeta (constantsOf sources))

abbrev thrLimits {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  CloseoutSampledWitness.thresholdLimits (selectedPCPP sources)
    (CloseoutWitnessPolicy.request sources k clock x oracle)
    (clauseWidth p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n))
    p.copies ⌊wireScale (1 / (den : ℝ)) 9 ((outer sources k clock).result.pcp.nativeWidth n)⌋₊
    (zeta (constantsOf sources))

abbrev SymFamily {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  SumFamily NormalizedSymmetricThresholdCircuit NormalizedSymmetricThresholdCircuit.wireCount
    NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p den x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)

abbrev ThrFamily {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  SumFamily NormalizedThresholdThresholdCircuit NormalizedThresholdThresholdCircuit.wireCount
    NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p den x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)

variable {n : ℕ} (x : BitInput n)
  (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)

def symFamilyOf : SymFamily sources k clock p den x oracle :=
  (SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
    NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p den x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
    (RadixSemantics.value (BoundedFields.family bits))).getD
      (trivialFamily _ _ _ (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies) _)

theorem symFamilyOf_pin (family : SymFamily sources k clock p den x oracle)
    (h : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    symFamilyOf sources k clock p den x oracle bits = family := by simp [symFamilyOf, h]

def thrFamilyOf : ThrFamily sources k clock p den x oracle :=
  (SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
    NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p den x oracle)
    (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
    (RadixSemantics.value (BoundedFields.family bits))).getD
      (trivialFamily _ _ _ (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies) _)

theorem thrFamilyOf_pin (family : ThrFamily sources k clock p den x oracle)
    (h : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    thrFamilyOf sources k clock p den x oracle bits = family := by simp [thrFamilyOf, h]

def proofValueOf : BitInput (CloseoutWitnessPolicy.request sources k clock x oracle).arity →
    Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle) → ℝ :=
  if BoundedFields.symmetric bits then
    SumFamily.value NormalizedSymmetricThresholdCircuit.eval (symFamilyOf sources k clock p den x oracle bits)
  else
    SumFamily.value NormalizedThresholdThresholdCircuit.eval (thrFamilyOf sources k clock p den x oracle bits)

theorem proofValueOf_sym (family : SymFamily sources k clock p den x oracle)
    (hs : BoundedFields.symmetric bits = true)
    (h : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    proofValueOf sources k clock p den x oracle bits =
      SumFamily.value NormalizedSymmetricThresholdCircuit.eval family := by
  simp [proofValueOf, hs, symFamilyOf_pin sources k clock p den x oracle bits family h]

theorem proofValueOf_thr (family : ThrFamily sources k clock p den x oracle)
    (hs : BoundedFields.symmetric bits = false)
    (h : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources k clock p den x oracle)
      (CloseoutWitnessPolicy.variableCount sources k clock x oracle)
      (RadixSemantics.value (BoundedFields.family bits)) = some family) :
    proofValueOf sources k clock p den x oracle bits =
      SumFamily.value NormalizedThresholdThresholdCircuit.eval family := by
  simp [proofValueOf, hs, thrFamilyOf_pin sources k clock p den x oracle bits family h]

end
end NearCubicWires.P1Independent.CappedDecode

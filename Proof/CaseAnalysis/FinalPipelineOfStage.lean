import Proof.CaseAnalysis.FinalFuelMajorant

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PipelineOfStage

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open C10TailComposeUniform C10TailCompose C10TotalDecode C10DecidesUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {gamma : ℝ} (sources : EightSources) (p : Parameters sources gamma) (k : ℕ)
  (S : StageData sources k p) (hs : StageBlock sources k p S)

def pipeline_of_stage : C10Fusion.Pipeline sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
    (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget :=
  fun n x bits =>
    PSum.inr ⟨oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits,
     Atoms sources k p x bits, proofOf sources k p x bits,
     evaluate (pcpp := pcppOf sources k p x bits), C10TailCompose.scr S.e,
     widthOf sources k p S x bits, verdict_of_stage sources k p S hs n x bits⟩

def pinnedSym_of_stage (s : ℕ) (_hs : Soundness.cutoff (constantsOf sources) ≤ s)
    (input : BitInput (2^s))
    (oracle : BooleanCircuit ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (family : SymFamily sources k (PolynomialClock.ordinaryClock k) p input oracle)
    (guess : BitInput (2^s/16))
    (_hlen : 16*(List.ofFn guess).length ≤ 2^s)
    (_hheader : CompetitorWitnessTriple.headerValid (List.ofFn guess))
    (horacle : decodeBooleanCircuit ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s))
      (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle)
    (hsize : oracle.size ≤ oracleSizeBound p.degree
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (hfamily : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (symLimits sources k (PolynomialClock.ordinaryClock k) p input oracle)
      (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) input oracle)
      (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family)
    (hmode : BoundedFields.symmetric (List.ofFn guess) = true) :
    PinnedSym' sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
      (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget p.clauseDegree p.copies
      (zeta (constantsOf sources)) 1 s input oracle family guess := by
  have ho := oracleOf_pin sources k (PolynomialClock.ordinaryClock k) p.degree (2^s)
    (List.ofFn guess) oracle horacle hsize
  subst oracle
  have hp : proofOf sources k p input (List.ofFn guess) =
      SumFamily.value NormalizedSymmetricThresholdCircuit.eval family :=
    proofValueOf_sym sources k (PolynomialClock.ordinaryClock k) p input _ (List.ofFn guess) family hmode hfamily
  refine ⟨Atoms sources k p input (List.ofFn guess),
    evaluate (pcpp := pcppOf sources k p input (List.ofFn guess)), C10TailCompose.scr S.e,
    widthOf sources k p S input (List.ofFn guess), ?_⟩
  rw [← hp]
  exact verdict_of_stage sources k p S hs (2^s) input (List.ofFn guess)

def pinnedThr_of_stage (s : ℕ) (_hs : Soundness.cutoff (constantsOf sources) ≤ s)
    (input : BitInput (2^s))
    (oracle : BooleanCircuit ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (family : ThrFamily sources k (PolynomialClock.ordinaryClock k) p input oracle)
    (guess : BitInput (2^s/16))
    (_hlen : 16*(List.ofFn guess).length ≤ 2^s)
    (_hheader : CompetitorWitnessTriple.headerValid (List.ofFn guess))
    (horacle : decodeBooleanCircuit ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s))
      (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle)
    (hsize : oracle.size ≤ oracleSizeBound p.degree
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (hfamily : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (thrLimits sources k (PolynomialClock.ordinaryClock k) p input oracle)
      (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) input oracle)
      (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family)
    (hmode : BoundedFields.symmetric (List.ofFn guess) = false) :
    PinnedThr' sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
      (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget p.clauseDegree p.copies
      (zeta (constantsOf sources)) 1 s input oracle family guess := by
  have ho := oracleOf_pin sources k (PolynomialClock.ordinaryClock k) p.degree (2^s)
    (List.ofFn guess) oracle horacle hsize
  subst oracle
  have hp : proofOf sources k p input (List.ofFn guess) =
      SumFamily.value NormalizedThresholdThresholdCircuit.eval family :=
    proofValueOf_thr sources k (PolynomialClock.ordinaryClock k) p input _ (List.ofFn guess) family hmode hfamily
  refine ⟨Atoms sources k p input (List.ofFn guess),
    evaluate (pcpp := pcppOf sources k p input (List.ofFn guess)), C10TailCompose.scr S.e,
    widthOf sources k p S input (List.ofFn guess), ?_⟩
  rw [← hp]
  exact verdict_of_stage sources k p S hs (2^s) input (List.ofFn guess)

def machine_of_stage : CloseoutFinal.Machine sources p.degree p.clauseDegree p.copies where
  k := k
  clock := PolynomialClock.ordinaryClock k
  tapes := bigOf S.e
  states := _
  worker := workerOf sources k p S hs
  htapes := bigTwo S.e
  result := gResult S.e
  fuel := S.budget
  pipeline := pipeline_of_stage sources p k S hs
  gateOnset := Soundness.cutoff (constantsOf sources)
  symCap := 1
  thrCap := 1
  hsym := by norm_num
  hthr := by norm_num
  symDecides := symDecides_of_pinned' sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
    (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget p.degree p.clauseDegree p.copies 1
    (Soundness.cutoff (constantsOf sources))
    (fun s h => h.trans (Nat.lt_two_pow_self).le) (pinnedSym_of_stage sources p k S hs)
  thrDecides := thrDecides_of_pinned' sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
    (workerOf sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget p.degree p.clauseDegree p.copies 1
    (Soundness.cutoff (constantsOf sources))
    (fun s h => h.trans (Nat.lt_two_pow_self).le) (pinnedThr_of_stage sources p k S hs)

end
end NearCubicWires.RepairSource.CloseoutFinal.C10PipelineOfStage

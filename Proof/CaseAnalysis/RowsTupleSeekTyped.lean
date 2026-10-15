import Proof.CaseAnalysis.RowsTupleSeekIndexed
import Proof.CaseAnalysis.RowsSupportTyped

/-! The synchronized slices are exactly the original typed native,
coefficient and declared-support bytes already emitted by the family run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics CloseoutWitness
open CloseoutRowsCircuitCanonicalFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def typedSlices {q : ℕ} (top : List Bool) (gs : List (SupportedNormalizedGate q)) (b : ℕ) (r : ℚ) : TermSlices :=
  ⟨top,![ [decide (r.num<0)],SignedSortKey.binary b r.num.natAbs,SignedSortKey.binary b r.den],
    gs.map (fun g=>(CloseoutRowsCircuitBottom.nativeWord g,CloseoutRowsGateSupport.gateMembers g.support))⟩

theorem typed_words {q : ℕ} (top : List Bool) (gs : List (SupportedNormalizedGate q)) (b : ℕ) (r : ℚ) :
    (typedSlices top gs b r).words=
      ![RepairRepresentation.natWord gs.length++frame top++gs.flatMap (fun g=>frame (CloseoutRowsCircuitBottom.nativeWord g)),
        CloseoutRowsSupportStream.supportWord gs,TermRecord.word b r,countWord gs.length] := by
  funext i;fin_cases i <;>
    simp [typedSlices,TermSlices.words,nativeWord,supportWord,record,TermRecord.word,
      CloseoutRowsSupportStream.supportWord,List.flatMap_map]

noncomputable def symmetricSlices {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) (C : ℕ) (bits : List Bool) :=
  typedSlices (List.ofFn c.top) (List.ofFn c.bottom) (natBitLength C) (TermChoice.rational (natBitLength C) bits)
noncomputable def thresholdSlices {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) (C : ℕ) (bits : List Bool) :=
  typedSlices (CloseoutRowsCircuitThresholdRun.top c.top) (List.ofFn (fun i=>c.bottom (retainedTopIndex c i)))
    (natBitLength C) (TermChoice.rational (natBitLength C) bits)

theorem symmetric_binding {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) (C : ℕ) (bits : List Bool)
    (hd : decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits))=some c) :
    (symmetricSlices c C bits).words=
      ![FamilyMode.native true core bits,CloseoutRowsSupportStream.FamilyMode.support true core bits,
        TermLoop.coefficientWord C bits,countWord c.bottomCount] := by
  have hn := (CloseoutRowsCircuitMeaning.symmetric_typed c 0 0 (TermCoefficient.circuitCode bits) hd).2
  have hs := CloseoutRowsSupportStream.Symmetric.support_typed c (TermCoefficient.circuitCode bits) hd
  simp only [symmetricSlices,typed_words,List.length_ofFn]
  funext i;fin_cases i
  · exact hn.symm
  · exact hs.symm
  · rfl
  · rfl

theorem threshold_binding {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) (C : ℕ) (bits : List Bool)
    (hd : decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits))=some c) :
    (thresholdSlices c C bits).words=
      ![FamilyMode.native false core bits,CloseoutRowsSupportStream.FamilyMode.support false core bits,
        TermLoop.coefficientWord C bits,countWord c.top.wireCount] := by
  have hn := (CloseoutRowsCircuitMeaning.threshold_typed c 0 0 (TermCoefficient.circuitCode bits) hd).2
  have hs := CloseoutRowsSupportStream.Threshold.support_typed c (TermCoefficient.circuitCode bits) hd
  simp only [FamilyMode.native,CloseoutRowsSupportStream.FamilyMode.support,Bool.false_eq_true,ite_false,
    CloseoutRowsCircuitTermSupplier.thresholdNative]
  rw [hn,hs]
  simp only [thresholdSlices,typed_words,List.length_ofFn]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek

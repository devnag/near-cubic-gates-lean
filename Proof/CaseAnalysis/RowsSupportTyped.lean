import Proof.CaseAnalysis.RowsSupportFamily
import Proof.CaseAnalysis.RowsSupportMeaning
import Proof.CaseAnalysis.RowsCircuitMeaning

/-! The actual retained bytes bind to precisely the same original gate
carrier as the native circuit segment. This includes selected THR bottom
occurrences and every declared zero-weight support incidence. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsCircuitWords CloseoutRowsCircuitCanonicalFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Symmetric.support_typed {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core) (bits : List Bool)
    (hd:decodeNormalizedSymmetricThresholdCircuit core (value bits)=some c):
    Symmetric.support core bits=supportWord (List.ofFn c.bottom):=by
  obtain ⟨_hp,hn,hbottom,_ht,_hvalid⟩:=symmetric_fields c bits hd
  unfold Symmetric.support
  rw [hn]
  exact support_symmetric c (words bits) [] 1 hbottom

theorem Threshold.support_typed {core : ℕ} (c : NormalizedThresholdThresholdCircuit core) (bits : List Bool)
    (hd:decodeNormalizedThresholdThresholdCircuit core (value bits)=some c):
    Threshold.support core bits=supportWord (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))):=by
  rcases c with ⟨n,bottom,topGate⟩
  obtain ⟨_hp,hn,hbottom,ht⟩:=threshold_fields ⟨n,bottom,topGate⟩ bits hd
  change (words bits).length=n at hn
  subst n
  let c : NormalizedThresholdThresholdCircuit core:=⟨(words bits).length,bottom,topGate⟩
  have hg:CloseoutRowsCircuitThresholdRun.decoded bits=some topGate:=by
    unfold CloseoutRowsCircuitThresholdRun.decoded
    rw [ht]
    exact decodeSupportedNormalizedGate_encode topGate
  unfold Threshold.support
  rw [hg]
  exact support_threshold c (words bits) hbottom

theorem supportWord_append {q : ℕ} (before selected after : List (SupportedNormalizedGate q)):
    supportWord (before++selected++after)=supportWord before++supportWord selected++supportWord after:=by
  simp only [supportWord,List.flatMap_append]

theorem supportWord_slice {q : ℕ} (before selected after : List (SupportedNormalizedGate q)):
    ((supportWord (before++selected++after)).drop (before.length*(2*q+1))).take (selected.length*(2*q+1))=
      supportWord selected:=by
  rw [supportWord_append,←supportWord_length before,←supportWord_length selected]
  simp only [List.append_assoc,List.drop_left,List.take_left]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream

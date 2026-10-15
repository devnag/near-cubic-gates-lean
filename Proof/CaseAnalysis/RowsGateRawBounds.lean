import Proof.CaseAnalysis.RowsGateRun

/-! Actual canonical component decoding bounds every count and binary
magnitude by the raw gate width. No numeric-magnitude unary field or
witness-declared count supplies the native writer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateRawBounds
open LocalBitMultitape RadixSemantics CanonicalBinary CloseoutWitness PCPPNativeCanonicalTree
open CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem list_count (bits : List Bool) (weights : List ℤ) (h : decodeIntList (value bits)=some weights) :
    weights.length ≤ bits.length+1 := by
  have hc := (CloseoutRowsIntegerList.checks_iff bits).mpr (by rw [h];rfl)
  obtain ⟨ws,_,hw,hlen,_⟩ := CloseoutRowsIntegerList.typed_of_checks bits hc
  have he : ws=weights := Option.some.inj (hw.symm.trans h)
  rw [←he,hlen]
  exact (CloseoutRowsIntegerList.fields_bound bits).1

theorem integer_bits (bits : List Bool) (z : ℤ) (h : decodeInt (value bits)=some z) :
    z.natAbs.bits.length ≤ bits.length+1 := by
  rw [←CloseoutRowsGateFieldsMeaning.threshold_payload bits z h]
  exact CloseoutRowsIntegerGuard.payload_bound bits

theorem list_bits (bits : List Bool) (weights : List ℤ) (h : decodeIntList (value bits)=some weights) :
    ∀ z∈weights,z.natAbs.bits.length ≤ bits.length+1 := by
  have hvalues : (Reencode.fields bits).map value=weights.map encodeInt := by
    change PCPSerializerMass.values (Reencode.fields bits)=_
    rw [Reencode.fields_values,←encodeIntList_of_decode h,encodeIntList,tree_atoms]
  intro z hz
  have hm : encodeInt z∈(Reencode.fields bits).map value := by
    rw [hvalues];exact List.mem_map_of_mem hz
  obtain ⟨word,hw,hvalue⟩ := List.mem_map.mp hm
  have hd : decodeInt (value word)=some z := by rw [hvalue,decodeInt_encode]
  have hb := integer_bits word z hd
  rw [(CloseoutRowsIntegerList.fields_bound bits).2 word hw] at hb
  exact hb

theorem members_count (bits : List Bool) (members : List Bool) (h : decodeBoolList (value bits)=some members) :
    members.length ≤ bits.length+1 := by
  have he := (CloseoutRowsBooleanVector.checks_of_typed members bits (encodeBoolList_of_decode h).symm).2
  rw [←he]
  simpa only [BitFields.payload,List.length_map] using (CloseoutRowsIntegerList.fields_bound bits).1

theorem fields_word (weights : List ℤ) :
    (CloseoutRowsGateDecisionMeaning.fields weights).flatMap fieldWord=weights.flatMap RepairRepresentation.intWord := by
  simp only [CloseoutRowsGateDecisionMeaning.fields,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro z _
  exact intField_word z

theorem fields_bound (bits : List Bool) (weights : List ℤ) (h : decodeIntList (value bits)=some weights) :
    ∀ field∈CloseoutRowsGateDecisionMeaning.fields weights,field.2.length ≤ bits.length+2 := by
  intro field hf
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hf
  have hb := list_bits bits weights h z hz
  have hn := PCPSerializerMass.value_width z.natAbs.bits
  rw [CanonicalPositiveOutput.nat_bits_value] at hn
  change (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs).length ≤ _
  rw [SignedSortKey.binary_length]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateRawBounds

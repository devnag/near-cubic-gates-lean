import Proof.CaseAnalysis.CloseoutRowsIntegerLoop

/-! The existing balanced-list verdict and the counted integer verdict are
exactly the canonical IntList decoder; their native output is the same list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerList
open LocalBitMultitape RadixSemantics CanonicalBinary CloseoutWitness PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def checks (bits : List Bool) : Prop:=
  (∃ codes,encodeBalancedList codes=value bits) ∧
    ∀ word∈Reencode.fields bits,(decodeInt (value word)).isSome
def decoded (word : List Bool) : ℤ:=(decodeInt (value word)).getD 0

theorem decoded_eq (word : List Bool) (h : (decodeInt (value word)).isSome) :
    decodeInt (value word)=some (decoded word):=by
  obtain ⟨z,hz⟩:=Option.isSome_iff_exists.mp h
  simp only [decoded,hz,Option.getD_some]

theorem typed_of_checks (bits : List Bool) (h : checks bits) :
    ∃ values : List ℤ,encodeIntList values=value bits ∧ decodeIntList (value bits)=some values ∧
      values.length=(Reencode.fields bits).length ∧
      (Reencode.fields bits).flatMap CloseoutRowsCheckedInteger.produced=
        values.flatMap RepairRepresentation.intWord:=by
  let values:=(Reencode.fields bits).map decoded
  have hc:values.map encodeInt=(Reencode.fields bits).map value:=by
    rw [List.map_map]
    apply List.map_congr_left
    intro word hw
    exact encodeInt_of_decode (decoded_eq word (h.2 word hw))
  have hcode:encodeIntList values=value bits:=by
    unfold encodeIntList
    rw [hc]
    change encodeBalancedList (PCPSerializerMass.values (Reencode.fields bits))=_
    rw [Reencode.fields_values]
    exact (tree_canonical_iff _).mpr h.1
  refine ⟨values,hcode,?_,List.length_map _,?_⟩
  · rw [←hcode,decodeIntList_encode]
  · change _=((Reencode.fields bits).map decoded).flatMap RepairRepresentation.intWord
    rw [List.flatMap_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro word hw
    exact CloseoutRowsIntegerLoop.produced_eq word _ (decoded_eq word (h.2 word hw))

theorem checks_of_typed (values : List ℤ) (bits : List Bool) (hcode : value bits=encodeIntList values) :
    checks bits:=by
  have hv:(Reencode.fields bits).map value=values.map encodeInt:=by
    change PCPSerializerMass.values (Reencode.fields bits)=_
    rw [Reencode.fields_values,hcode,encodeIntList,tree_atoms]
  refine ⟨⟨values.map encodeInt,hcode.symm⟩,?_⟩
  intro word hw
  have hm:value word∈values.map encodeInt:=by
    rw [←hv]
    exact List.mem_map_of_mem hw
  obtain ⟨z,_,hz⟩:=List.mem_map.mp hm
  rw [←hz,decodeInt_encode]
  rfl

theorem checks_iff (bits : List Bool) : checks bits ↔ (decodeIntList (value bits)).isSome:=by
  constructor
  · intro h
    obtain ⟨values,_,hv,_⟩:=typed_of_checks bits h
    exact Option.isSome_iff_exists.mpr ⟨values,hv⟩
  · intro h
    obtain ⟨values,hv⟩:=Option.isSome_iff_exists.mp h
    exact checks_of_typed values bits (encodeIntList_of_decode hv).symm

theorem fields_bound (bits : List Bool) :
    (Reencode.fields bits).length≤bits.length+1 ∧ ∀ word∈Reencode.fields bits,word.length=bits.length:=by
  refine ⟨?_,?_⟩
  · simpa only [Reencode.fields,List.length_map,TraversalCounted.count] using Reencode.count_bound bits
  · intro word hw
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hw
    exact SignedSortKey.binary_length _ a

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerList

import Proof.CaseAnalysis.WitnessNat

/-! The retained vector flag accepts the canonical Boolean list, including
a final false bit. It is the support/top-table consumer of the shared scan. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBooleanVector
open LocalBitMultitape RadixSemantics CanonicalBinary CloseoutWitness PCPPNativeCanonicalTree SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def checks (bits : List Bool) : Prop:=
  (∃ codes,encodeBalancedList codes=value bits) ∧ (Reencode.fields bits).all BitFields.good=true

theorem code_of_checks (bits : List Bool) (h : checks bits) :
    encodeBoolList (BitFields.payload bits)=value bits:=by
  have hm:PCPSerializerMass.values (Reencode.fields bits)=(BitFields.payload bits).map boolCode:=by
    unfold PCPSerializerMass.values BitFields.payload
    simp only [List.map_map,Function.comp_def]
    exact List.map_congr_left (fun word hw=>BitFields.good_value word ((List.all_eq_true.mp h.2) word hw))
  unfold encodeBoolList
  rw [←hm,Reencode.fields_values]
  exact (tree_canonical_iff _).mpr h.1

theorem checks_of_typed (values : List Bool) (bits : List Bool) (hcode : value bits=encodeBoolList values) :
    checks bits ∧ BitFields.payload bits=values:=by
  have hf:Reencode.fields bits=(values.map boolCode).map (binary bits.length):=by
    unfold Reencode.fields
    rw [hcode,encodeBoolList,tree_atoms]
  by_cases hw:bits.length=0
  · have he:bits=[]:=List.length_eq_zero_iff.mp hw
    subst bits
    have hv:values=[]:=by
      have hd:=congrArg decodeBoolList hcode
      rw [show value []=encodeBoolList [] by simp [value,encodeBoolList,encodeBalancedList]] at hd
      simpa only [decodeBoolList_encode,Option.some.injEq] using hd.symm
    subst values
    have hnil:Reencode.fields []=[]:=by simpa only [List.map_nil] using hf
    refine ⟨⟨⟨[],by simp [encodeBalancedList,value]⟩,?_⟩,?_⟩
    · rw [hnil]
      rfl
    · simp only [BitFields.payload,hnil,List.map_nil]
  · have hpos:0<bits.length:=Nat.pos_of_ne_zero hw
    refine ⟨⟨⟨values.map boolCode,hcode.symm⟩,?_⟩,?_⟩
    · rw [hf,List.all_eq_true]
      intro word hm
      obtain ⟨code,hc,rfl⟩:=List.mem_map.mp hm
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp hc
      exact (BitFields.binary_bool _ hpos b).1
    · unfold BitFields.payload
      rw [hf,List.map_map,List.map_map]
      calc
        _=values.map id:=List.map_congr_left (fun b _=>(BitFields.binary_bool _ hpos b).2)
        _=values:=List.map_id _

theorem checks_iff (bits : List Bool) : checks bits ↔ (decodeBoolList (value bits)).isSome:=by
  constructor
  · intro h
    rw [←code_of_checks bits h,decodeBoolList_encode]
    rfl
  · intro h
    obtain ⟨values,hv⟩:=Option.isSome_iff_exists.mp h
    exact (checks_of_typed values bits (encodeBoolList_of_decode hv).symm).1

end NearCubicWires.RepairOrdinary.CloseoutRowsBooleanVector

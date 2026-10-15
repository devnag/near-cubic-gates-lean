import Proof.CaseAnalysis.WitnessNodeLoop

/-! The physical header, balanced-list, natural-field and counted-node
tests are exactly the existing public Boolean-circuit decoder. The output
descriptor uses their retained fields, including the actual output address. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGChecks
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec CanonicalBinary
open PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words (bits : List Bool):=Reencode.fields (PCPPNativeCanonical.nodeWord bits)
def output (bits : List Bool):=value (BitFields.payload (PCPPNativeCanonical.outputWord bits))
def checks (n : ℕ) (bits : List Bool) : Prop:=
  PCPPNativeCanonical.headerValid bits ∧
  (∃ values,encodeBalancedList values=value (PCPPNativeCanonical.nodeWord bits)) ∧
  BitFields.passes (PCPPNativeCanonical.outputWord bits) ∧
  (∀ i : Fin (words bits).length,NodeMeaning.valid n i.val ((words bits).get i)) ∧
  output bits<(words bits).length

theorem typed_of_checks (n : ℕ) (bits : List Bool) (h : checks n bits) :
    ∃ circuit : BooleanCircuit n,
      encodeBooleanCircuit circuit=value bits ∧ decodeBooleanCircuit n (value bits)=some circuit ∧
      circuit.nodes.length=(words bits).length ∧ circuit.output.val=output bits ∧
      PCPPNative.descriptor circuit=
        RepairRepresentation.natWord n++RepairRepresentation.natWord (words bits).length++
          (words bits).flatMap DAGMeaning.emitted++RepairRepresentation.natWord (output bits):=by
  obtain ⟨circuit,hcount,hout,hcode,hdecode,hnative⟩:=
    DAGMeaning.typed_dag n (output bits) (words bits) h.2.2.2.1 h.2.2.2.2
  have hlist:encodeBalancedList ((words bits).map value)=value (PCPPNativeCanonical.nodeWord bits):=by
    change encodeBalancedList (PCPSerializerMass.values (Reencode.fields _))=_
    rw [Reencode.fields_values]
    exact (tree_canonical_iff _).mpr h.2.1
  have hnat:encodeNat (output bits)=value (PCPPNativeCanonical.outputWord bits):=
    BitFields.code_of_passes _ h.2.2.1
  have hraw:encodeTaggedList [encodeBalancedList ((words bits).map value),encodeNat (output bits)]=value bits:=by
    rw [hlist,hnat]
    exact ((PCPPNativeCanonical.header_valid_iff bits).mp h.1).symm
  rw [hraw] at hcode hdecode
  exact ⟨circuit,hcode,hdecode,hcount,hout,hnative⟩

theorem checks_of_typed {n : ℕ} (circuit : BooleanCircuit n) (bits : List Bool)
    (hc : value bits=encodeBooleanCircuit circuit) : checks n bits:=by
  obtain ⟨hh,hnodes,hout⟩:=PCPPNativeCanonical.circuit_values circuit bits hc
  have hp:=BitFields.encoded_passes (PCPPNativeCanonical.outputWord bits) circuit.output.val hout
  have hv:(words bits).map value=circuit.nodes.map encodeBooleanNode:=by
    change PCPSerializerMass.values (Reencode.fields _)=_
    rw [Reencode.fields_values,hnodes,tree_atoms]
  have hlen:(words bits).length=circuit.nodes.length:=by
    simpa only [List.length_map] using congrArg List.length hv
  have ho:output bits=circuit.output.val:=by
    have h:=BitFields.decode_of_passes _ hp.1
    rw [hout,decodeNat_encode] at h
    exact (Option.some.inj h).symm
  refine ⟨hh,⟨circuit.nodes.map encodeBooleanNode,hnodes.symm⟩,hp.1,?_,?_⟩
  · intro i
    let j : Fin circuit.nodes.length:=Fin.cast hlen i
    have hi:i.val<circuit.nodes.length:=by rw [←hlen];exact i.isLt
    apply NodeMeaning.valid_of_node (circuit.nodes.get j) i.val ((words bits).get i)
      (circuit.wellFormed j)
    have he:=congrArg (fun xs : List ℕ=>xs.getD i.val 0) hv
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),
      List.getElem_map,List.getElem_map] at he
    exact he
  · rw [ho,hlen]
    exact circuit.output.isLt

theorem checks_iff (n : ℕ) (bits : List Bool) :
    checks n bits ↔ (decodeBooleanCircuit n (value bits)).isSome:=by
  constructor
  · intro h
    obtain ⟨c,_,hc,_⟩:=typed_of_checks n bits h
    exact Option.isSome_iff_exists.mpr ⟨c,hc⟩
  · intro h
    obtain ⟨c,hc⟩:=Option.isSome_iff_exists.mp h
    exact checks_of_typed c bits (encodeBooleanCircuit_of_decode hc).symm

theorem fields_bound (bits : List Bool) :
    (words bits).length≤(PCPPNativeCanonical.nodeWord bits).length+1 ∧
    ∀ word∈words bits,word.length=(PCPPNativeCanonical.nodeWord bits).length:=by
  refine ⟨?_,?_⟩
  · simpa only [words,Reencode.fields,List.length_map,TraversalCounted.count] using
      Reencode.count_bound (PCPPNativeCanonical.nodeWord bits)
  · intro word hw
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hw
    exact SignedSortKey.binary_length _ a

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGChecks

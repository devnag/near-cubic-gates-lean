import Proof.CaseAnalysis.WitnessNodeBody
import Proof.PCP.PCPPNativeRequestSchema

/-! The same accepted node fields determine both the canonical typed DAG
and the literal native descriptor consumed by the PCPP source. This is a
semantic join; it introduces no new parser or normalization algorithm. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGMeaning
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emitted (bits : List Bool) : List Bool:=
  (List.ofFn (fun j=>NativeWord.word (NodeBody.payloads bits j))).flatten

theorem native_fields (n index : ℕ) (bits : List Bool) (h : NodeMeaning.valid n index bits) :
    emitted bits=(List.ofFn (fun j : Fin 3=>RepairRepresentation.natWord (NodeMeaning.number bits j))).flatten:=by
  unfold emitted
  congr 1
  apply congrArg List.ofFn
  funext j
  exact NativeWord.word_eq _ ((BitFields.last_iff _).mp (h.1 j).2.2)

theorem typed_dag (n output : ℕ) (words : List (List Bool))
    (hvalid : ∀ i : Fin words.length,NodeMeaning.valid n i.val (words.get i))
    (houtput : output<words.length) :
    ∃ circuit : BooleanCircuit n,
      circuit.nodes.length=words.length ∧ circuit.output.val=output ∧
      encodeBooleanCircuit circuit=
        encodeTaggedList [encodeBalancedList (words.map value),encodeNat output] ∧
      decodeBooleanCircuit n
        (encodeTaggedList [encodeBalancedList (words.map value),encodeNat output])=some circuit ∧
      PCPPNative.descriptor circuit=
        RepairRepresentation.natWord n++RepairRepresentation.natWord words.length++
          words.flatMap emitted++RepairRepresentation.natWord output:=by
  classical
  have hex (i : Fin words.length):∃ node : BooleanNode n,
      node.WellFormedAt i.val ∧ encodeBooleanNode node=value (words.get i) ∧
        PCPPRequestNodeSchema.native node=emitted (words.get i):=by
    obtain ⟨node,hw,hcode,hnative⟩:=NodeMeaning.node_of_valid n i.val (words.get i) (hvalid i)
    exact ⟨node,hw,hcode,hnative.trans (native_fields n i.val _ (hvalid i)).symm⟩
  choose nodes hw hcode hnative using hex
  let circuit : BooleanCircuit n:={
    nodes:=List.ofFn nodes
    output:=⟨output,by simpa only [List.length_ofFn] using houtput⟩
    wellFormed:=by
      intro i
      rw [List.get_ofFn]
      exact hw (Fin.cast (by simp) i) }
  have hc:(List.ofFn nodes).map encodeBooleanNode=words.map value:=by
    rw [List.map_ofFn]
    have he:List.ofFn (fun i=>encodeBooleanNode (nodes i))=
        List.ofFn (fun i=>value (words.get i)):=congrArg List.ofFn (funext hcode)
    exact he.trans (by rw [List.ofFn_comp',List.ofFn_get])
  have hn:(List.ofFn nodes).flatMap PCPPRequestNodeSchema.native=words.flatMap emitted:=by
    change ((List.ofFn nodes).map PCPPRequestNodeSchema.native).flatten=(words.map emitted).flatten
    congr 1
    rw [List.map_ofFn]
    have he:List.ofFn (fun i=>PCPPRequestNodeSchema.native (nodes i))=
        List.ofFn (fun i=>emitted (words.get i)):=congrArg List.ofFn (funext hnative)
    exact he.trans (by rw [List.ofFn_comp',List.ofFn_get])
  have henc:encodeBooleanCircuit circuit=
      encodeTaggedList [encodeBalancedList (words.map value),encodeNat output]:=by
    change encodeTaggedList [encodeBalancedList ((List.ofFn nodes).map encodeBooleanNode),encodeNat output]=_
    rw [hc]
  refine ⟨circuit,List.length_ofFn,rfl,henc,?_,?_⟩
  · rw [←henc,decodeBooleanCircuit_encode]
  · rw [PCPPNative.descriptor_eq]
    change RepairRepresentation.natWord n++RepairRepresentation.natWord (List.ofFn nodes).length++
      (List.ofFn nodes).flatMap PCPPRequestNodeSchema.native++RepairRepresentation.natWord output=_
    rw [List.length_ofFn,hn]

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGMeaning

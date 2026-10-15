import Proof.Amplification.RecoveryQueryCell

/-! The literal constant-depth prefix-query spine and its corrected-oracle
meaning. The balanced base payload is retained unchanged by prefix search. -/
namespace NearCubicWires.RepairSource.RecoveryQuery
open CanonicalBinary BalancedCNFSATEncoding RecoveryOracle
open RepairOrdinary
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def node0 (count : Nat) := Nat.pair 1 count
def node1 (count : Nat) := Nat.pair (node0 count) 0+1
def node2 (committed : Nat) := Nat.pair 0 committed
def node3 (committed count : Nat) := Nat.pair (node2 committed) (node1 count)+1
def node4 (committed count : Nat) := Nat.pair (node3 committed count) 0+1
def node5 (flat : Bool) (payload : Nat) := Nat.pair flat.toNat payload
def node6 (flat : Bool) (payload : Nat) := Nat.pair (node5 flat payload) 0+1
def node7 (flat : Bool) (payload committed count : Nat) :=
  Nat.pair (node6 flat payload) (node4 committed count)+1
def node8 (flat : Bool) (payload committed count : Nat) :=
  Nat.pair 0 (node7 flat payload committed count)+1
def code (flat : Bool) (payload committed count : Nat) :=
  if flat then encodeBalancedPrefixCNFPayload payload committed count
  else encodeNestedBalancedPrefixCNFPayloadMarker payload committed count
def operations : Fin 9→Bool := ![false,true,false,true,true,false,true,true,true]
def lefts (flat : Bool) (payload committed count : Nat) : Fin 9→Nat :=
  ![1,node0 count,0,node2 committed,node3 committed count,flat.toNat,node5 flat payload,
    node6 flat payload,0]
def rights (flat : Bool) (payload committed count : Nat) : Fin 9→Nat :=
  ![count,0,committed,node1 count,0,payload,0,node4 committed count,node7 flat payload committed count]
def values (flat : Bool) (payload committed count : Nat) : Fin 9→Nat :=
  ![node0 count,node1 count,node2 committed,node3 committed count,node4 committed count,
    node5 flat payload,node6 flat payload,node7 flat payload committed count,node8 flat payload committed count]

theorem node_result (flat : Bool) (payload committed count : Nat) (j : Fin 9) :
    RecoveryQueryCell.result (operations j) (lefts flat payload committed count j)
      (rights flat payload committed count j)=values flat payload committed count j := by
  fin_cases j <;> rfl

theorem exact_code (flat : Bool) (payload committed count : Nat) :
    node8 flat payload committed count=code flat payload committed count := by
  cases flat <;>
    simp [code,node8,node7,node6,node5,node4,node3,node2,node1,node0,
      encodeBalancedPrefixCNFPayload,encodeNestedBalancedPrefixCNFPayloadMarker,
      balancedPrefixCNFMarkerOfPayload,nestedBalancedPrefixCNFMarkerOfPayload,
      Encodable.encode_list_cons,Encodable.encode_prod_val,
      Encodable.encode_false,Encodable.encode_true]

def PayloadDecodes (flat : Bool) (payload : Nat) (formula : EncodedCNF) : Prop :=
  (if flat then decodeBalancedList payload else decodeNestedBalancedCNFPayload payload)=
    some (formula.map Encodable.encode)

theorem query_meaning (flat : Bool) (payload committed count : Nat) (formula : EncodedCNF)
    (hp : PayloadDecodes flat payload formula) :
    correctedSat (code flat payload committed count)=true ↔
      compactMeaning ⟨formula,committed,count⟩ := by
  rw [←correctedWitnessVerifier_iff]
  cases flat
  · have hd : decodeCNF (code false payload committed count)=
        nestedBalancedPrefixCNFMarkerOfPayload payload committed count := by
      simp [code,decodeCNF,encodeNestedBalancedPrefixCNFPayloadMarker,Encodable.encodek]
    have hz : wellSizedCNFEncoding (code false payload committed count)
        (decodeCNF (code false payload committed count))=false := by
      rw [hd]
      simp [wellSizedCNFEncoding,nestedBalancedPrefixCNFMarkerOfPayload]
    have hn : decodeNestedCompact (code false payload committed count)=some ⟨formula,committed,count⟩ := by
      simp only [PayloadDecodes,Bool.false_eq_true,if_false] at hp
      simp [decodeNestedCompact,hd,nestedBalancedPrefixCNFMarkerOfPayload,hp,
        decodeClauseCodes,Encodable.encodek,Function.comp_def]
    have hf : decodeFlatCompact (code false payload committed count)=none := by
      simp [decodeFlatCompact,hd,nestedBalancedPrefixCNFMarkerOfPayload]
    simp only [correctedWitnessVerifier,hz,Bool.false_eq_true,if_false,hf,hn]
    exact compactVerifier_iff _
  · have hd : decodeCNF (code true payload committed count)=
        balancedPrefixCNFMarkerOfPayload payload committed count := by
      simp [code,decodeCNF,encodeBalancedPrefixCNFPayload,Encodable.encodek]
    have hz : wellSizedCNFEncoding (code true payload committed count)
        (decodeCNF (code true payload committed count))=false := by
      rw [hd]
      simp [wellSizedCNFEncoding,balancedPrefixCNFMarkerOfPayload]
    have hf : decodeFlatCompact (code true payload committed count)=some ⟨formula,committed,count⟩ := by
      simp only [PayloadDecodes,if_true] at hp
      simp [decodeFlatCompact,hd,balancedPrefixCNFMarkerOfPayload,hp,
        decodeClauseCodes,Encodable.encodek,Function.comp_def]
    simp only [correctedWitnessVerifier,hz,Bool.false_eq_true,if_false,hf]
    exact compactVerifier_iff _

end NearCubicWires.RepairSource.RecoveryQuery

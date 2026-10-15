import Proof.CaseAnalysis.WitnessNatNative
import Proof.PCP.PCPPNativeCanonicalGuard

/-! The node consumer checks literal native fields before any unary node
reader. Its tag, input bound, and strict earlier-node bounds are exactly the
canonical Boolean DAG's existing typing rules. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeMeaning
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalBinary
open CanonicalWitnessCodec CompetitorWitnessTriple PCPPRequestNodeSchema
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def test (n index tag a b : ℕ) : Prop := match tag with
  | 0=>a ≤ 1 ∧ b=0
  | 1=>a < n ∧ b=0
  | 2=>a < index ∧ b=0
  | 3=>a < index ∧ b < index
  | 4=>a < index ∧ b < index
  | _=>False

theorem fields_test {n : ℕ} (node : BooleanNode n) (index : ℕ)
    (h : node.WellFormedAt index) :
    test n index (fields node 0) (fields node 1) (fields node 2) := by
  cases node with
  | const b=>cases b <;> simp [test,fields]
  | input i=>exact ⟨i.isLt,rfl⟩
  | not a=>exact ⟨h,rfl⟩
  | and a b=>exact h
  | or a b=>exact h

theorem node_of_test (n index tag a b : ℕ) (h : test n index tag a b) :
    ∃ node : BooleanNode n,node.WellFormedAt index ∧ fields node=![tag,a,b] := by
  rcases tag with _|_|_|_|_|tag
  · change a ≤ 1 ∧ b=0 at h
    rcases h with ⟨ha,rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl|rfl
    · exact ⟨.const false,True.intro,rfl⟩
    · exact ⟨.const true,True.intro,rfl⟩
  · change a < n ∧ b=0 at h
    rcases h with ⟨ha,rfl⟩
    exact ⟨.input ⟨a,ha⟩,True.intro,rfl⟩
  · change a < index ∧ b=0 at h
    rcases h with ⟨ha,rfl⟩
    exact ⟨.not a,ha,rfl⟩
  · exact ⟨.and a b,h,rfl⟩
  · exact ⟨.or a b,h,rfl⟩
  · contradiction

def codeWord (bits : List Bool) (i : Fin 3):=
  RecoveryFixedUnpair.leftWord (word bits (2*i.val+1))
def number (bits : List Bool) (i : Fin 3):=value (BitFields.payload (codeWord bits i))
def naturals (bits : List Bool) : Prop:=∀ i,BitFields.passes (codeWord bits i)
def shape (bits : List Bool) : Prop:=
  if 3 ≤ number bits 0 then structural bits else PCPPNativeCanonical.headerValid bits
def valid (n index : ℕ) (bits : List Bool) : Prop:=
  naturals bits ∧ shape bits ∧ test n index (number bits 0) (number bits 1) (number bits 2)

theorem number_code (bits : List Bool) (h : naturals bits) (i : Fin 3) :
    encodeNat (number bits i)=field bits (2*i.val+1):=BitFields.code_of_passes _ (h i)

theorem node_of_valid (n index : ℕ) (bits : List Bool) (h : valid n index bits) :
    ∃ node : BooleanNode n,node.WellFormedAt index ∧ encodeBooleanNode node=value bits ∧
      native node=(List.ofFn (fun i : Fin 3=>RepairRepresentation.natWord (number bits i))).flatten := by
  obtain ⟨node,hw,hfields⟩:=node_of_test n index _ _ _ h.2.2
  have ht:(tag node).val=number bits 0:=by rw [←first_tag,hfields];rfl
  have h0:=number_code bits h.1 0
  have h1:=number_code bits h.1 1
  have h2:=number_code bits h.1 2
  refine ⟨node,hw,?_,?_⟩
  · rw [code_eq,binaryNode,ht]
    by_cases hb:3 ≤ number bits 0
    · rw [decide_eq_true hb,if_pos (by rfl),hfields]
      change encodeTaggedList [encodeNat (number bits 0),encodeNat (number bits 1),encodeNat (number bits 2)]=value bits
      rw [h0,h1,h2]
      exact ((structural_iff bits).mp (by simpa only [shape,if_pos hb] using h.2.1)).symm
    · rw [decide_eq_false hb,if_neg (by decide),hfields]
      change encodeTaggedList [encodeNat (number bits 0),encodeNat (number bits 1)]=value bits
      rw [h0,h1]
      exact ((PCPPNativeCanonical.header_valid_iff bits).mp (by
        simpa only [shape,if_neg hb] using h.2.1)).symm
  · rw [native,hfields]
    simp [List.ofFn_succ]

theorem accepted_numeric_bound (n index : ℕ) (bits : List Bool) (h : valid n index bits) (i : Fin 3) :
    number bits i ≤ n+index+4 := by
  obtain ⟨node,hw,hfields⟩:=node_of_test n index _ _ _ h.2.2
  have hb:=field_bound node index hw i
  rw [hfields] at hb
  fin_cases i <;> exact hb

theorem encoded_fields {n : ℕ} (node : BooleanNode n) (bits : List Bool)
    (h : value bits=encodeBooleanNode node) (i : Fin 3) :
    value (codeWord bits i)=encodeNat (fields node i) := by
  change field bits (2*i.val+1)=_
  rw [field_eq,h]
  have hz:encodeNat 0=0:=CompetitorWitnessTriple.encoded_modes.1
  cases node <;> fin_cases i <;>
    simp [encodeBooleanNode,fields,nodeCode,encodeTaggedList,hz]

theorem valid_of_node {n : ℕ} (node : BooleanNode n) (index : ℕ) (bits : List Bool)
    (hw : node.WellFormedAt index) (h : value bits=encodeBooleanNode node) : valid n index bits := by
  have hp (i : Fin 3):BitFields.passes (codeWord bits i) ∧
      BitFields.payload (codeWord bits i)=(fields node i).bits:=
    BitFields.encoded_passes _ _ (encoded_fields node bits h i)
  have hv (i : Fin 3):number bits i=fields node i:=by
    have hd:=BitFields.decode_of_passes _ (hp i).1
    rw [encoded_fields node bits h i,decodeNat_encode] at hd
    exact (Option.some.inj hd).symm
  refine ⟨fun i=>(hp i).1,?_,?_⟩
  · unfold shape
    rw [hv]
    have h0:field bits 1=encodeNat (fields node 0):=encoded_fields node bits h 0
    have h1:field bits 3=encodeNat (fields node 1):=encoded_fields node bits h 1
    have h2:field bits 5=encodeNat (fields node 2):=encoded_fields node bits h 2
    by_cases hb:3 ≤ fields node 0
    · rw [if_pos hb]
      apply (structural_iff bits).mpr
      rw [h0,h1,h2,h,code_eq,binaryNode,←first_tag,decide_eq_true hb,if_pos (by rfl)]
    · rw [if_neg hb]
      apply (PCPPNativeCanonical.header_valid_iff bits).mpr
      change value bits=encodeTaggedList [field bits 1,field bits 3]
      rw [h0,h1,h,code_eq,binaryNode,←first_tag,decide_eq_false hb,if_neg (by decide)]
  · rw [hv,hv,hv]
    exact fields_test node index hw

theorem valid_iff (n index : ℕ) (bits : List Bool) : valid n index bits ↔
    ∃ node : BooleanNode n,node.WellFormedAt index ∧ decodeBooleanNode n (value bits)=some node := by
  constructor
  · intro h
    obtain ⟨node,hw,hcode,_⟩:=node_of_valid n index bits h
    exact ⟨node,hw,by rw [←hcode,decodeBooleanNode_encode]⟩
  · rintro ⟨node,hw,hdecode⟩
    exact valid_of_node node index bits hw (encodeBooleanNode_of_decode hdecode).symm

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeMeaning

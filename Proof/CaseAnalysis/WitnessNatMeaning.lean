import Proof.CaseAnalysis.WitnessBitFieldsRun

/-! The field reader's tests are exactly canonical natural-number decoding.
High zero padding in an individual atom is harmless; a zero high payload bit
in the decoded natural is rejected by the existing codec convention. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields
open LocalBitMultitape RadixSemantics CanonicalBinary SignedSortKey
open PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_zero (bits : List Bool) : value bits=0 ↔ bits.any id=false := by
  induction bits with
  | nil=>simp [value]
  | cons b bits ih=>cases b <;> simp [value,List.any_cons,ih]

theorem good_iff (field : List Bool) : good field=true ↔ field≠[] ∧ value field ≤ 1 := by
  cases field with
  | nil=>simp [good]
  | cons b rest=>
    simp only [good,Bool.not_eq_true_eq_eq_false]
    rw [←value_zero rest]
    cases b <;> simp [value]
    omega

theorem good_value (field : List Bool) (h : good field=true) : value field=boolCode (lower field) := by
  cases field with
  | nil=>simp [good] at h
  | cons b rest=>
    have hz:value rest=0:=(value_zero rest).mpr (by simpa only [good,Bool.not_eq_true_eq_eq_false] using h)
    cases b <;> simp [value,hz,boolCode,lower]

theorem binary_bool (w : ℕ) (hw : 0<w) (b : Bool) :
    good (binary w (boolCode b))=true ∧ lower (binary w (boolCode b))=b := by
  have hpow:1<2^w:=lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide : 0<2) hw)
  have hb:boolCode b<2^w:=by cases b <;> simp only [boolCode,Bool.toNat_false,Bool.toNat_true] <;> omega
  have hvalue:=binary_value w (boolCode b) hb
  have hg:good (binary w (boolCode b))=true:=(good_iff _).mpr ⟨by
    intro he
    have hl:=binary_length w (boolCode b)
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega,by rw [hvalue];cases b <;> decide⟩
  refine ⟨hg,?_⟩
  have hcode:=hvalue.symm.trans (good_value _ hg)
  have he:(lower (binary w (boolCode b))).toNat=b.toNat:=hcode.symm
  generalize hq:lower (binary w (boolCode b))=q at he ⊢
  cases q <;> cases b
  all_goals first | rfl | norm_num only [Bool.toNat_false,Bool.toNat_true] at he

theorem last_iff (fields : List (List Bool)) :
    last true fields=true ↔ fields.map lower=[] ∨ (fields.map lower).getLast?=some true := by
  induction fields with
  | nil=>simp [last]
  | cons field fields ih=>
    cases fields with
    | nil=>simp [last]
    | cons field' fields=>simpa only [last,List.map_cons,List.getLast?_cons_cons,List.cons_ne_nil,
        false_or] using ih

theorem canonical_bits (bits : List Bool) (h : bits=[] ∨ bits.getLast?=some true) :
    (value bits).bits=bits := by
  induction bits with
  | nil=>rfl
  | cons b rest ih=>
    cases rest with
    | nil=>rcases h with h|h <;> cases b <;> simp_all [value]
    | cons c rest=>
      have hr:(c::rest).getLast?=some true:=by simpa using h
      have hi:=ih (Or.inr hr)
      have hn:value (c::rest)≠0:=by
        intro hz
        rw [hz,Nat.zero_bits] at hi
        simp at hi
      have he:value (b::c::rest)=Nat.bit b (value (c::rest)):=by cases b <;> simp [value,Nat.bit];omega
      rw [he,Nat.bits_append_bit _ _ (by intro hz;exact (hn hz).elim),hi]

def payload (bits : List Bool) := (Reencode.fields bits).map lower
def passes (bits : List Bool) : Prop :=
  (∃ values,encodeBalancedList values=value bits) ∧
    (Reencode.fields bits).all good=true ∧ last true (Reencode.fields bits)=true
noncomputable instance (bits : List Bool) : Decidable (passes bits) := Classical.propDecidable _

theorem code_of_passes (bits : List Bool) (h : passes bits) :
    encodeNat (value (payload bits))=value bits := by
  have hcanonical:encodeBalancedList (tree (value bits)).atoms=value bits:=
    (tree_canonical_iff _).mpr h.1
  have hmap:PCPSerializerMass.values (Reencode.fields bits)=(payload bits).map boolCode:=by
    unfold PCPSerializerMass.values payload
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro field hf
    exact good_value field ((List.all_eq_true.mp h.2.1) field hf)
  have hbits:((value (payload bits)).bits)=payload bits:=
    canonical_bits _ ((last_iff _).mp h.2.2)
  rw [encodeNat,hbits]
  change encodeBalancedList ((payload bits).map boolCode)=value bits
  rw [←hmap,Reencode.fields_values,hcanonical]

theorem encoded_passes (bits : List Bool) (n : ℕ) (h : value bits=encodeNat n) :
    passes bits ∧ payload bits=n.bits := by
  have hf:Reencode.fields bits=(n.bits.map boolCode).map (binary bits.length):=by
    unfold Reencode.fields
    rw [h]
    change (tree (encodeBalancedList (n.bits.map boolCode))).atoms.map _=_
    rw [tree_atoms]
  by_cases hw:bits.length=0
  · have he:bits=[]:=List.length_eq_zero_iff.mp hw
    subst bits
    have hn:n=0:=by
      have hd:=congrArg decodeNat h
      rw [decodeNat_encode] at hd
      have he:(some 0 : Option ℕ)=some n:=by
        simpa only [show value []=encodeNat 0 by simp [value,encodeNat,encodeBits,encodeBoolList,encodeBalancedList],decodeNat_encode] using hd
      exact (Option.some.inj he).symm
    subst n
    have hf0:Reencode.fields []=[]:=by simpa only [Nat.zero_bits,List.map_nil] using hf
    constructor
    · exact ⟨⟨[],by simp [value,encodeBalancedList]⟩,by rw [hf0];rfl,by rw [hf0];rfl⟩
    · simp only [payload,hf0,List.map_nil,Nat.zero_bits]
  · have hpos:0<bits.length:=Nat.pos_of_ne_zero hw
    have hp:payload bits=n.bits:=by
      unfold payload
      rw [hf]
      simp only [List.map_map,Function.comp_def]
      calc
        _=n.bits.map id:=List.map_congr_left (fun b _=>(binary_bool _ hpos b).2)
        _=n.bits:=List.map_id _
    refine ⟨⟨⟨n.bits.map boolCode,h.symm⟩,?_,?_⟩,hp⟩
    · rw [hf,List.all_eq_true]
      intro field hfield
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hfield
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
      exact (binary_bool _ hpos b).1
    · apply (last_iff _).mpr
      change payload bits=[] ∨ (payload bits).getLast?=some true
      rw [hp]
      exact CanonicalBinary.Nat.bits_canonical n

theorem passes_iff (bits : List Bool) : passes bits ↔ (decodeNat (value bits)).isSome := by
  constructor
  · intro h
    rw [←code_of_passes bits h,decodeNat_encode]
    rfl
  · intro h
    obtain ⟨n,hn⟩:=Option.isSome_iff_exists.mp h
    exact (encoded_passes bits n (encodeNat_of_decode hn).symm).1

theorem decode_of_passes (bits : List Bool) (h : passes bits) :
    decodeNat (value bits)=some (value (payload bits)) := by
  rw [←code_of_passes bits h,decodeNat_encode]

end NearCubicWires.RepairOrdinary.CloseoutWitness.BitFields

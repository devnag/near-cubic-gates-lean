import Proof.PCP.PCPPairCanonical

/-! The serializer's workspace parameter is bounded by measured framed
input bytes. Stored tree nodes use canonical bits after each paid pair call,
so the existing balanced-code theorem bounds every retained subtree. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerMass
open RadixSemantics CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mass (fields : List (List Bool)) : ℕ := (fields.map (fun bits => 2*bits.length+1)).sum
def values (fields : List (List Bool)) : List ℕ := fields.map value

theorem value_width (bits : List Bool) : natBitLength (value bits) ≤ bits.length+1 := by
  by_cases hz : value bits=0
  · simp [hz,natBitLength]
  · have h := Nat.log_lt_of_lt_pow hz (value_lt bits)
    unfold natBitLength
    omega

theorem mass_bounds (fields : List (List Bool)) :
    fields.length ≤ mass fields ∧ ((values fields).map natBitLength).sum ≤ mass fields := by
  induction fields with
  | nil => simp [mass,values]
  | cons bits fields ih =>
    have hb := value_width bits
    simp only [mass,values,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    constructor <;> omega

theorem code_width (fields : List (List Bool)) :
    natBitLength (encodeBalancedList (values fields)) ≤ 3*(mass fields+1)^5 := by
  have h := balancedListCodeBits_le (values fields)
  obtain ⟨hn,ha⟩ := mass_bounds fields
  have hn' : (values fields).length ≤ mass fields+1 := by
    simpa only [values,List.length_map] using (hn.trans (Nat.le_succ _))
  have ha' : balancedListAtomBits (values fields) ≤ mass fields+1 := by
    unfold balancedListAtomBits
    omega
  have hm : 1+2*(values fields).length^4*balancedListAtomBits (values fields) ≤
      1+2*(mass fields+1)^4*(mass fields+1) := by gcongr
  have he : 1+2*(mass fields+1)^4*(mass fields+1)=1+2*(mass fields+1)^5 := by ring
  have hp : 1 ≤ (mass fields+1)^5 := Nat.one_le_pow 5 _ (by omega)
  exact h.trans (hm.trans (by rw [he]; omega))

theorem nat_bits_width (n : ℕ) : n.bits.length ≤ natBitLength n := by
  have h : n.size ≤ Nat.log 2 n+1 := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) n)
  exact (Nat.size_eq_bits_len n).le.trans h

theorem code_bits (fields : List (List Bool)) :
    (encodeBalancedList (values fields)).bits.length ≤ 3*(mass fields+1)^5 :=
  (nat_bits_width _).trans (code_width fields)

theorem mass_append (left right : List (List Bool)) :
    mass (left++right)=mass left+mass right := by simp [mass]

theorem split_mass (fields : List (List Bool)) (n : ℕ) :
    mass (fields.take n) ≤ mass fields ∧ mass (fields.drop n) ≤ mass fields := by
  have h := mass_append (fields.take n) (fields.drop n)
  rw [List.take_append_drop] at h
  omega

end NearCubicWires.RepairOrdinary.PCPSerializerMass

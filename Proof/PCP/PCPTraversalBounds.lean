import Proof.PCP.PCPTraversalEntry

/-! Width and stack reserves at the literal midpoint-recursive caller.
Intermediate untagged pairs are bounded by the tagged subtree code, so the
already accepted common pair capacity also covers the final tag-two call. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open CanonicalBinary PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (fields : List (List Bool)) := encodeBalancedList (values fields)
def midpoint (fields : List (List Bool)) := (fields.length+1)/2
def leftFields (fields : List (List Bool)) := fields.take (midpoint fields)
def rightFields (fields : List (List Bool)) := fields.drop (midpoint fields)
def frameBound (B : ℕ) := 7*(B+1)^5

theorem stream_mass (fields : List (List Bool)) : (FieldList.stream fields).length=mass fields := by
  induction fields with
  | nil => rfl
  | cons bits fields ih =>
    simp only [FieldList.stream,List.map_cons,List.flatten_cons,List.length_append,frame_length,
      mass,List.sum_cons] at ih ⊢
    omega

theorem split_lengths (fields : List (List Bool)) (h : 2≤fields.length) :
    0<(leftFields fields).length ∧ 0<(rightFields fields).length ∧
    (leftFields fields).length<fields.length ∧ (rightFields fields).length<fields.length ∧
    (leftFields fields).length+(rightFields fields).length=fields.length ∧
    (rightFields fields).length=fields.length/2 := by
  simp only [leftFields,rightFields,midpoint,List.length_take,List.length_drop]
  omega

theorem split_code (fields : List (List Bool)) (h : 2≤fields.length) :
    code fields=Nat.pair 2 (Nat.pair (code (leftFields fields)) (code (rightFields fields))) := by
  cases fields with
  | nil => simp at h
  | cons a fields =>
    cases fields with
    | nil => simp at h
    | cons b fields =>
      simp only [code,values,List.map_cons,encodeBalancedList,leftFields,rightFields,midpoint,
        List.length_cons,List.length_map,List.map_take,List.map_drop]

theorem positive_code (fields : List (List Bool)) (h : 0<fields.length) : 0<code fields := by
  have he := encodeBalancedList_length_le (values fields)
  simp only [values,List.length_map] at he
  exact h.trans_le he

theorem bounded_code (fields : List (List Bool)) (B : ℕ) (h : mass fields≤B) :
    (code fields).bits.length≤3*(B+1)^5 := by
  have ht := code_bits fields
  exact ht.trans (by gcongr)

theorem bounded_frame (fields : List (List Bool)) (B : ℕ) (h : mass fields≤B) :
    (frame (code fields).bits).length≤frameBound B := by
  rw [frame_length]
  have hc := bounded_code fields B h
  have hp := Nat.one_le_pow 5 (B+1) (by omega)
  dsimp [frameBound]
  omega

theorem bounded_inner (fields : List (List Bool)) (B : ℕ)
    (h : mass fields≤B) (hn : 2≤fields.length) :
    (Nat.pair (code (leftFields fields)) (code (rightFields fields))).bits.length≤3*(B+1)^5 := by
  have hp := Nat.right_le_pair 2 (Nat.pair (code (leftFields fields)) (code (rightFields fields)))
  rw [←split_code fields hn] at hp
  have hm := PolynomialClock.natBitLength_mono hp
  have hw := code_width fields
  exact (nat_bits_width _).trans (hm.trans (hw.trans (by gcongr)))

theorem capacity_reserves (B : ℕ) :
    B*frameBound B+3*B+3≤PCPPairReusable.capacity B := by
  have h5 : 1≤(B+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have h6 : (B+1)^6≤(B+1)^10 := pow_le_pow_right₀ (by omega) (by omega)
  have hb : B+1≤(B+1)^6 := by
    calc
      B+1=(B+1)^1 := by simp
      _≤(B+1)^6 := pow_le_pow_right₀ (by omega) (by omega)
  have hm : B*frameBound B≤7*(B+1)^6 := by
    unfold frameBound
    calc
      B*(7*(B+1)^5)≤(B+1)*(7*(B+1)^5) := by gcongr; omega
      _=7*(B+1)^6 := by ring
  unfold PCPPairReusable.capacity
  omega

theorem split_reserves (B n l r leftPrefix rightPrefix contPrefix : ℕ)
    (hn : l+r=n) (hl : 0<l) (hr : 0<r)
    (hleft : leftPrefix+n*frameBound B≤PCPPairReusable.capacity B)
    (hright : rightPrefix+3*n≤PCPPairReusable.capacity B)
    (hcont : contPrefix+2*n≤PCPPairReusable.capacity B) :
    leftPrefix+frameBound B+r*frameBound B≤PCPPairReusable.capacity B ∧
    rightPrefix+(2*r+1)+3*l≤PCPPairReusable.capacity B ∧
    contPrefix+2+2*l≤PCPPairReusable.capacity B ∧
    contPrefix+2+2*r≤PCPPairReusable.capacity B := by
  have hm : (r+1)*frameBound B≤n*frameBound B := by gcongr; omega
  rw [Nat.add_mul,Nat.one_mul] at hm
  omega

end NearCubicWires.RepairOrdinary.PCPTraversal

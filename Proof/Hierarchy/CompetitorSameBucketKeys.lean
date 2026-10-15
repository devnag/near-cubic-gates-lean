import Proof.Hierarchy.CompetitorSameBucketPackets

/-! The exact internal signed-contribution record uses the existing signed
coefficient and occurrence-ID fields. Grouping compares the two ID fields;
payload differences cannot interleave distinct row-major cells. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketKeys
open LocalBitMultitape MatrixScoreBatch SignedSortKey RadixSemantics StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload (p : ℕ) (coefficient : ℤ) := true::signMagnitude p coefficient
def key (p k : ℕ) (coefficient : ℤ) (leftID rightID : ℕ) : Record :=
  (true,signMagnitude p coefficient++binary k rightID++binary k leftID)

@[simp] theorem key_word (p k : ℕ) (coefficient : ℤ) (leftID rightID : ℕ) :
    word (key p k coefficient leftID rightID)=payload p coefficient++(binary k rightID++binary k leftID) := by
  simp only [key,RadixSemantics.word,payload,List.append_assoc]
  rfl

@[simp] theorem payload_length (p : ℕ) (coefficient : ℤ) : (payload p coefficient).length=p+2 := by
  simp [payload]

@[simp] theorem key_width (p k : ℕ) (coefficient : ℤ) (leftID rightID : ℕ) :
    (word (key p k coefficient leftID rightID)).length=p+2+2*k := by
  simp
  omega

theorem key_value (p k : ℕ) (coefficient : ℤ) (leftID rightID : ℕ)
    (hl : leftID<2^k) (hr : rightID<2^k) :
    value (word (key p k coefficient leftID rightID))=
      value (payload p coefficient)+2^(p+2)*(rightID+2^k*leftID) := by
  rw [key_word,value_append,payload_length,value_append,binary_value _ _ hr,binary_length,binary_value _ _ hl]

theorem key_order (p k : ℕ) (c d : ℤ) (a b a' b' : ℕ)
    (ha : a<2^k) (hb : b<2^k) (ha' : a'<2^k) (hb' : b'<2^k)
    (horder : value (word (key p k c a b))≤value (word (key p k d a' b'))) :
    a<a' ∨ a=a' ∧ b≤b' := by
  have hp : value (payload p c)<2^(p+2) := by simpa using value_lt (payload p c)
  have hq : value (payload p d)<2^(p+2) := by simpa using value_lt (payload p d)
  rw [key_value _ _ _ _ _ ha hb,key_value _ _ _ _ _ ha' hb',numeric_key_le_iff _ _ _ _ _ hp hq] at horder
  have hcoord : b+2^k*a≤b'+2^k*a' := by rcases horder with h|⟨h,_⟩ <;> omega
  exact (numeric_key_le_iff _ _ _ _ _ hb hb').mp hcoord

theorem same_cell_iff (u a b a' b' : ℕ) :
    a=a' ∧ u+b=u+b' ↔ a=a' ∧ b=b' := by omega

def zeroRecords (p k u : ℕ) : List Record :=
  (List.finRange u).flatMap (fun row => (List.finRange u).map (fun column => key p k 0 row.val (u+column.val)))

theorem zero_count (p k u : ℕ) : (zeroRecords p k u).length=u*u := by
  simp [zeroRecords,List.length_flatMap]

theorem zero_present (p k u : ℕ) (row column : Fin u) :
    key p k 0 row.val (u+column.val)∈zeroRecords p k u := by
  apply List.mem_flatMap.mpr
  refine ⟨row,by simp,?_⟩
  apply List.mem_map.mpr
  exact ⟨column,by simp,rfl⟩

theorem zero_width (p k u : ℕ) : ∀ e∈zeroRecords p k u,(word e).length=p+2+2*k := by
  intro e he
  obtain ⟨row,_,he⟩ := List.mem_flatMap.mp he
  obtain ⟨column,_,rfl⟩ := List.mem_map.mp he
  exact key_width _ _ _ _ _

end NearCubicWires.RepairOrdinary.CompetitorSameBucketKeys

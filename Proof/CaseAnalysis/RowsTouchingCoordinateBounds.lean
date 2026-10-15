import Proof.CaseAnalysis.RowsTouchingCoordinateLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (q w P : ℕ) (st : Store):Prop:=
  Gate.Valid q w P st.gate ∧ st.left.length≤2*w+1 ∧ st.right.length≤2*w+1

theorem product_fits (q G w n a : ℕ) (hn:n≤q) (ha:a≤G*2^q) (hw:2*q+G≤w):n*a<2^w:=by
  have hp:0<2^q:=by positivity
  have hq:q≤2^q:=(Nat.lt_two_pow_self).le
  have hG:G<2^G:=Nat.lt_two_pow_self
  calc
    n*a≤2^q*(G*2^q):=Nat.mul_le_mul (hn.trans hq) ha
    _ <2^q*(2^G*2^q):=Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hG hp) hp
    _ =2^(2*q+G):=by rw [←Nat.pow_add,←Nat.pow_add];congr 1;omega
    _ ≤2^w:=Nat.pow_le_pow_right (by decide : 0<2) hw

theorem scratch_bound (w a n : ℕ) (old : List Bool) (hb:old.length≤2*w+1):
    (UnaryProduct.scratch w a n old).length≤2*w+1:=by
  unfold UnaryProduct.scratch
  split
  · exact hb
  · simp [frame_length,binary_length]

theorem chosen_scratch (w k h : ℕ) (st : Store):
    (chosen w k h st).gate.scratch=UnaryProduct.scratch w st.gate.included h
      (UnaryProduct.scratch w st.gate.excluded k st.gate.scratch):=rfl

theorem chosen_valid (q k h w P : ℕ) (st : Store) (hv:Gate.Valid q w P st.gate):
    Valid q w P (chosen w k h st):=by
  have hs:(chosen w k h st).gate.scratch.length≤2*w+1:=by
    rw [chosen_scratch]
    exact scratch_bound w st.gate.included h _ (scratch_bound w st.gate.excluded k _ hv.2.2.2)
  refine ⟨⟨hv.1,hv.2.1,hv.2.2.1,hs⟩,?_,?_⟩
  · change (Choice.after w st.gate.excluded st.gate.included k h (choiceStore st)).left.length≤2*w+1
    rw [(Choice.after_fields _ _ _ _ _ _).1]
    simp [frame_length,binary_length]
  · change (Choice.after w st.gate.excluded st.gate.included k h (choiceStore st)).right.length≤2*w+1
    rw [(Choice.after_fields _ _ _ _ _ _).2.1]
    simp [frame_length,binary_length]

theorem cleared_valid (q w P : ℕ) (st : Store) (mode : Bool) (hv:Valid q w P st):
    Valid q w P (cleared st mode):=hv

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate

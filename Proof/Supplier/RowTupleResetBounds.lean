import Proof.Supplier.RowTupleCursorEquation

/-! The three changing tuple fields fit the same actual source-derived
allocation already used by the equation consumer. This pays their physical
erasure without another runtime capacity. -/
namespace NearCubicWires.RepairOrdinary.RowTupleResetBounds
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem occurrence_length (N : ℕ) (is : List (Fin N)) :
    (RowOccurrenceLoop.word is).length≤N*is.length := by
  induction is with
  | nil => simp [RowOccurrenceLoop.word]
  | cons i is ih =>
    have hi:=i.isLt
    simp only [RowOccurrenceLoop.word,List.flatMap_cons,List.length_append,
      RowIndexField.word,List.length_replicate,List.length_cons,List.length_nil] at *
    nlinarith

theorem fields_fit {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ)
    (is : List (Fin gs.length)) (hF : RowCommonBounds.capacity gs is.length p≤F) :
    n+3≤F ∧ (RowOccurrenceLoop.word is).length≤F ∧ is.length+1≤F := by
  let S:=RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)
  have hn : n+1≤S := by
    have h : n+1≤(n+1)*(gs.length+1) := by nlinarith
    unfold S RowCachedCoordinateBounds.size
    omega
  have hN : gs.length≤S := by
    have h : gs.length+1≤(n+1)*(gs.length+1) := by nlinarith
    unfold S RowCachedCoordinateBounds.size
    omega
  have h1 : 1≤S := by omega
  have ha : S≤(is.length+1)*S := by nlinarith
  have hb : is.length+1≤(is.length+1)*S := by nlinarith
  have hc : gs.length*is.length≤(is.length+1)*S := by
    have h:=Nat.mul_le_mul_right is.length hN
    nlinarith
  have hcap : (is.length+1)*S+64≤F := by
    have h : (is.length+1)*S≤16384*(is.length+1)*S := by nlinarith
    unfold RowCommonBounds.capacity at hF
    change 16384*(is.length+1)*S+16*p+64≤F at hF
    omega
  have hword:=occurrence_length gs.length is
  exact ⟨by omega,by omega,by omega⟩

end NearCubicWires.RepairOrdinary.RowTupleResetBounds

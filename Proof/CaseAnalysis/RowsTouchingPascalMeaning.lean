import Proof.CaseAnalysis.RowsTouchingPascalRow

/-! The streaming row consumes adjacent entries of the full Pascal row,
including its zero tail. The leading one is copied from the prior row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalRow
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def row (w m q : ℕ):=(List.range (q+1)).flatMap (fun k=>field w (Nat.choose m k))
def pairs (m q : ℕ):=(List.range q).map (fun k=>(Nat.choose m k,Nat.choose m (k+1)))

theorem left_row (w m q : ℕ):
    row w m q=(pairs m q).flatMap (leftWord w)++field w (Nat.choose m q):=by
  simp only [row,pairs,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.flatMap_map,leftWord]

theorem right_row (w m q : ℕ):
    row w m q=field w 1++(pairs m q).flatMap (rightWord w):=by
  rw [row,List.range_succ_eq_map]
  simp only [List.flatMap_cons,Nat.choose_zero_right,List.flatMap_map,pairs,rightWord]

theorem next_row (w m q : ℕ):
    row w (m+1) q=field w 1++(pairs m q).flatMap (sumWord w):=by
  rw [row,List.range_succ_eq_map]
  simp only [List.flatMap_cons,Nat.choose_zero_right,List.flatMap_map,pairs,sumWord,
    Nat.choose_succ_succ]

theorem row_length (w m q : ℕ):(row w m q).length=(q+1)*(2*w+1):=by
  unfold row
  rw [List.length_flatMap]
  simp only [field,frame_length,binary_length,List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul]
  rfl

theorem pairs_fit (q m : ℕ) (hm:m<q):
    ∀ pair∈pairs m q,pair.1+pair.2<2^(q+1):=by
  intro pair hp
  obtain ⟨k,_hk,rfl⟩:=List.mem_map.mp hp
  exact PascalCell.choose_fit q m k hm

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalRow

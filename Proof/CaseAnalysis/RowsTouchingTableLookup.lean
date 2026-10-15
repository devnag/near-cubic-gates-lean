import Proof.CaseAnalysis.RowsTouchingLookup

/-! The physical table lookup returns the natural binomial at its original
row/column indices. No address or binomial value is supplied as metadata. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.TableLookup
open LocalBitMultitape ExtDecompositionBatch SignedSortKey CloseoutRowsFamilyLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_parts (q m k : ℕ) (hm:m≤q) (hk:k≤q):∃ (before front : List (List Bool)) (tail : List Bool),
    before.length=m ∧ front.length=k ∧
    (∀ row∈before,row.length=PascalReady.width q) ∧
    (∀ word∈front,word.length=q+1) ∧
    PascalTable.table q=before.flatten++front.flatMap frame++frame (binary (q+1) (Nat.choose m k))++tail:=by
  let indices:=List.range (q+1)
  let before:=(indices.take m).map (fun j=>PascalRow.row (q+1) j q)
  let front:=(indices.take k).map (fun j=>binary (q+1) (Nat.choose m j))
  let tail:=(indices.drop (k+1)).flatMap (fun j=>PascalRow.field (q+1) (Nat.choose m j))++
    (indices.drop (m+1)).flatMap (fun j=>PascalRow.row (q+1) j q)
  have im:m < indices.length:=by simp only [indices,List.length_range];omega
  have ik:k < indices.length:=by simp only [indices,List.length_range];omega
  have gm:indices.getD m 0=m:=by rw [List.getD_eq_getElem indices 0 im];simp [indices]
  have gk:indices.getD k 0=k:=by rw [List.getD_eq_getElem indices 0 ik];simp [indices]
  have split:=split_word indices 0 (fun j=>PascalRow.row (q+1) j q) m im
  have cell:=split_word indices 0 (fun j=>PascalRow.field (q+1) (Nat.choose m j)) k ik
  rw [gm] at split
  rw [gk] at cell
  refine ⟨before,front,tail,?_,?_,?_,?_,?_⟩
  · simp only [before,List.length_map,List.length_take];omega
  · simp only [front,List.length_map,List.length_take];omega
  · intro row hr
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hr
    exact PascalRow.row_length (q+1) j q
  · intro word hw
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hw
    exact binary_length _ _
  · change indices.flatMap (fun j=>PascalRow.row (q+1) j q)=_
    rw [split]
    change (indices.take m).flatMap (fun j=>PascalRow.row (q+1) j q)++
      indices.flatMap (fun j=>PascalRow.field (q+1) (Nat.choose m j))++_= _
    rw [cell]
    simp only [before,front,tail,←List.flatMap_def,List.flatMap_map,PascalRow.field,List.append_assoc]

theorem lookup_run (q m k : ℕ) (backing : List Bool) (hm:m≤q) (hk:k≤q)
    (hb:backing.length≤2*(q+1)+1):
    Step Lookup.machine (Lookup.budget (PascalReady.width q) (q+1) m k) (Lookup.heads 0)
      (Lookup.data (PascalReady.width q) (q+1) m k (PascalTable.table q) backing)
      (Lookup.heads (m*PascalReady.width q+k*(2*(q+1)+1)+2*(q+1)+1))
      (Lookup.data (PascalReady.width q) (q+1) m k (PascalTable.table q)
        (frame (binary (q+1) (Nat.choose m k)))):=by
  obtain ⟨before,front,tail,hl,hlp,hw,hwp,split⟩:=table_parts q m k hm hk
  have actual:=Lookup.lookup_run (PascalReady.width q) (q+1) before front
    (binary (q+1) (Nat.choose m k)) tail backing hw (by intro word hh;exact (hwp word hh).le)
    (binary_length _ _) hb
  rw [hl,hlp,←split] at actual
  have bl:before.flatten.length=m*PascalReady.width q:=by
    rw [List.length_flatten]
    have h:before.map List.length=List.replicate before.length (PascalReady.width q):=List.map_eq_replicate_iff.mpr hw
    rw [h,List.sum_replicate,hl];simp
  have pl:(front.flatMap frame).length=k*(2*(q+1)+1):=by
    simp only [List.length_flatMap]
    have h:front.map (fun x=>(frame x).length)=List.replicate front.length (2*(q+1)+1):=by
      apply List.map_eq_replicate_iff.mpr
      intro x hx;rw [frame_length',hwp x hx]
    rw [h,List.sum_replicate,hlp];simp
  rw [bl,pl] at actual
  exact actual

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.TableLookup

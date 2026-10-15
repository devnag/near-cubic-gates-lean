import Proof.Supplier.RowTupleList

/-! The complete equation list consumes the actual checked enumeration
order. Width and validity of every tuple are discharged from the filter;
no selected tuple list or occurrence multiplicity is changed. -/
namespace NearCubicWires.RepairOrdinary.RowTupleSelectedList
open LocalBitMultitape RepairRepresentation
open RowTupleSubsets RowTupleDigits RowTupleList
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_fields (w M k : ℕ) (ds : List ℕ) (hd:ds∈selected w M k) :
    ds.length=k ∧ ∀ d∈ds,d<M := by
  obtain ⟨hc,hv⟩:=List.mem_filter.mp hd
  exact ⟨((candidates_mem w k ds).mp hc).1,((valid_iff M ds).mp hv).2⟩

theorem stream_eq (w M k : ℕ) : stream w (selected w M k)=RowTupleEnumeration.word w k M := by
  unfold stream RowTupleEnumeration.word
  have h : ∀ xs : List (List ℕ),(∀ ds∈xs,ds.length=k) →
      xs.flatMap (RowTupleFramedBody.word w)=xs.flatMap (fun ds=>frame (SignedSortKey.binary (w*k+1) (encode w ds))) := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons ds xs ih =>
      simp only [List.flatMap_cons,RowTupleFramedBody.word,hx ds (by simp)]
      rw [ih (fun d hd=>hx d (List.mem_cons_of_mem ds hd))]
  exact h _ (fun ds hd=>(selected_fields w M k ds hd).1)

theorem selected_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w k : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw:rows.length<2^w) (hk:k≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom RowTupleList.machine
      (RowTupleList.budget gs F w rows.length rows (selected w rows.length k))
      (cfg RowTupleList.machine.start gs p F w rows.length k rows (RowTupleEnumeration.word w k rows.length) 0 out 0)=some r ∧
      r.final.tapes 31=out++output gs p rows (selected w rows.length k) ∧
      r.final.heads 31=(out++output gs p rows (selected w rows.length k)).length ∧
      r.steps≤RowTupleList.budget gs F w rows.length rows (selected w rows.length k) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=list_run gs p F Q w rows.length k rows (selected w rows.length k) [] out 0
    hl (fun ds hd=>(selected_fields w rows.length k ds hd).1)
    (fun ds hd=>(selected_fields w rows.length k ds hd).2) hw le_rfl hk hp hF
  simp only [List.nil_append,List.length_nil,Nat.zero_add,stream_eq] at hr rh rt
  refine ⟨r,hr,?_,?_,rs⟩
  · rw [rt]
    exact (fields RowTupleList.machine.start gs p F w rows.length k rows _ _ _ _).2.2.1
  · rw [rh]
    exact (fields RowTupleList.machine.start gs p F w rows.length k rows _ _ _ _).2.2.2

end NearCubicWires.RepairOrdinary.RowTupleSelectedList

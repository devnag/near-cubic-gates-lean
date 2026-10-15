import Proof.Supplier.RowTupleOutputBody

/-! The executed output is an occurrence list of selected position tuples.
No set conversion or deduplication appears in its binary enumeration. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputMeaning
open LocalBitMultitape RowTupleFilterParts RowTupleFilterMeaning RowTupleOutputParts
open RowTupleOutputBody RowTupleDigits RowTupleSubsets SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fold_bound (x : Data) (ds : List ℕ) : (fold x ds).bound=x.bound := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => exact (ih _).trans (RowTupleFilterBody.advance_fields x d).2.1

theorem fold_previous (w : ℕ) (x : Data) (ds : List ℕ)
    (hp : x.previous<2^w) (hd : ∀ d∈ds,d<2^w) : (fold x ds).previous<2^w := by
  induction ds generalizing x with
  | nil => exact hp
  | cons d ds ih =>
    apply ih
    · rw [(RowTupleFilterBody.advance_fields x d).2.2.2.1]
      exact hd d (by simp)
    · intro a ha; exact hd a (List.mem_cons_of_mem _ ha)

theorem updated_fields (w k n : ℕ) (x : Data) (hp : x.previous<2^w) :
    (updated w k n x).source=frame (binary (w*k+1) (n+1)) ∧
    (updated w k n x).bound=x.bound ∧ (updated w k n x).previous<2^w := by
  refine ⟨rfl,?_,?_⟩
  · exact fold_bound _ _
  · exact fold_previous w (RowTupleCandidate.restarted x) _ hp (digits_bound w k n)

def entryWord (w k M n : ℕ) : List Bool :=
  if valid M (digits w k n) then frame (binary (w*k+1) n) else []
def output (w k M n count : ℕ) : List Bool :=
  (List.range' n count).flatMap (entryWord w k M)
def iterated (w k : ℕ) : ℕ→ℕ→Data→Data
  | _,0,x=>x
  | n,count+1,x=>iterated w k (n+1) count (updated w k n x)

theorem emitted_eq (w k M n : ℕ) (x : Data) (hM : 0<M)
    (hb : x.bound=M-1) (hx : x.source=frame (binary (w*k+1) n)) :
    emitted (filtered w k n x)=entryWord w k M n := by
  have hg := RowTupleFilterReusable.flag_meaning w k n M (RowTupleCandidate.restarted x) hM hb rfl rfl
  have hs := fold_source (RowTupleCandidate.restarted x) (digits w k n)
  change (filtered w k n x).source=x.source at hs
  simp only [emitted,filtered,hg,entryWord]
  rw [show (fold (RowTupleCandidate.restarted x) (digits w k n)).source=frame (binary (w*k+1) n) from hs.trans hx]

theorem output_succ (w k M n count : ℕ) :
    output w k M n (count+1)=entryWord w k M n++output w k M (n+1) count := by
  simp [output,List.range'_succ]

theorem full_output (w k M : ℕ) :
    output w k M 0 (2^(w*k))=
      (selected w M k).flatMap (fun ds=>frame (binary (w*k+1) (encode w ds))) := by
  have he (n : ℕ) (hn : n∈List.range (2^(w*k))) :
      entryWord w k M n=
        if valid M (digits w k n) then frame (binary (w*k+1) (encode w (digits w k n))) else [] := by
    rw [encode_digits w k n (List.mem_range.mp hn)]
    rfl
  unfold output selected candidates
  rw [←List.range_eq_range']
  rw [List.filter_map,List.flatMap_map]
  have filter_flat {α : Type} (xs : List α) (p : α→Bool) (f : α→List Bool) :
      (xs.filter p).flatMap f=xs.flatMap (fun x=>if p x then f x else []) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => cases h : p x <;> simp [h,ih]
  rw [filter_flat]
  apply List.flatMap_congr
  intro n hn
  exact he n hn

end NearCubicWires.RepairOrdinary.RowTupleOutputMeaning

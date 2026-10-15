import Proof.Hierarchy.CompetitorSameBucketDenseBounds

/-! The physical rank annotator stores the canonical stable dominance rank
of each genuine occurrence. This identifies the exact sorted packet, rather
than introducing an independently certified layout. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketRankMeaning
open MatrixScoreBatch SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ranked (r : Request) (g : Fin r.Gates) (copy : StableDominanceCopy r.U r.U) : KeyLoop.Record :=
  (stableDominanceCopyScore (leftScore r) (rightScore r) g copy,
    (stableDominanceCopyId copy).val,(stableDominanceRank (leftScore r) (rightScore r) g copy).val)

theorem indexed_get (n : ℕ) (xs : List (ℤ×ℕ)) (i : ℕ) (hi : i < xs.length) :
    (KeyLoop.indexed n xs)[i]'(by simpa only [KeyLoop.indexed_length] using hi)=
      (xs[i].1,xs[i].2,n+i) := by
  induction xs generalizing n i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases x with ⟨score,id⟩
    cases i with
    | zero => simp [KeyLoop.indexed]
    | succ i =>
      have hit : i < xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      simpa only [KeyLoop.indexed,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using ih (n+1) i hit

theorem entries_eq (r : Request) (g : Fin r.Gates) :
    MatrixScoreRawRanks.entries r g=
      (DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g).map (ranked r g) := by
  apply List.ext_getElem
  · simp only [MatrixScoreRawRanks.entries,KeyLoop.indexed_length,KeyLoop.dominanceEntries,List.length_map]
  · intro i hi hj
    have hip : i < (DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g).length := by
      simpa only [MatrixScoreRawRanks.entries,KeyLoop.indexed_length,KeyLoop.dominanceEntries,List.length_map] using hi
    simp only [MatrixScoreRawRanks.entries,KeyLoop.dominanceEntries]
    rw [indexed_get 0 _ i (by simpa only [List.length_map] using hip)]
    simp only [List.getElem_map,Nat.zero_add]
    have hr:=DominanceSort.sorted_rank r.S r.M (leftScore r) (rightScore r) g
      (MatrixScoreRawRanks.size_fit r) (score_lo r g) (score_hi r g) ⟨i,hip⟩
    change (stableDominanceRank (leftScore r) (rightScore r) g
      (DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g)[i]).val=i at hr
    simp only [ranked,hr]

theorem copy_present (r : Request) (g : Fin r.Gates) (copy : StableDominanceCopy r.U r.U) :
    ranked r g copy∈MatrixScoreRawRanks.entries r g := by
  rw [entries_eq]
  apply List.mem_map.mpr
  refine ⟨copy,?_,rfl⟩
  apply (DominanceSort.sorted_semantics r.S r.M (leftScore r) (rightScore r) g
    (MatrixScoreRawRanks.size_fit r) (score_lo r g) (score_hi r g)).1.mem_iff.mpr
  apply List.mem_ofFn.mpr
  exact ⟨stableDominanceCopyId copy,finSumFinEquiv.symm_apply_apply copy⟩

theorem entries_member (r : Request) (g : Fin r.Gates) (e : KeyLoop.Record) :
    e∈MatrixScoreRawRanks.entries r g ↔ ∃ copy,e=ranked r g copy := by
  constructor
  · rw [entries_eq]
    intro he
    obtain ⟨copy,_,rfl⟩:=List.mem_map.mp he
    exact ⟨copy,rfl⟩
  · rintro ⟨copy,rfl⟩
    exact copy_present r g copy

theorem ranked_id_injective (r : Request) (g : Fin r.Gates)
    (a b : StableDominanceCopy r.U r.U) (h : (ranked r g a).2.1=(ranked r g b).2.1) : a=b := by
  apply finSumFinEquiv.injective
  exact Fin.ext h

theorem ranked_left (r : Request) (g : Fin r.Gates) (row : Fin r.U) :
    (ranked r g (.inl row)).2.1=row.val := rfl
theorem ranked_right (r : Request) (g : Fin r.Gates) (col : Fin r.U) :
    (ranked r g (.inr col)).2.1=r.U+col.val := rfl

theorem rank_comparison (r : Request) (g : Fin r.Gates) (row col : Fin r.U) :
    (ranked r g (.inl row)).2.2 < (ranked r g (.inr col)).2.2 ↔ leftScore r row g ≤ rightScore r g col :=
  stableDominanceRank_left_lt_right_iff (leftScore r) (rightScore r) row g col

theorem indexed_rank_position (xs : List (ℤ×ℕ)) (padding i : ℕ) (e : KeyLoop.Record)
    (he : ((KeyLoop.indexed 0 xs).map some++List.replicate padding none)[i]?=some (some e)) :
    e.2.2=i := by
  by_cases hi : i < xs.length
  · have hl : i < ((KeyLoop.indexed 0 xs).map some).length := by simpa using hi
    rw [List.getElem?_append_left hl,List.getElem?_eq_getElem hl,List.getElem_map,indexed_get 0 xs i hi] at he
    have hh := Option.some.inj (Option.some.inj he)
    simpa only [Nat.zero_add] using (congrArg (fun a : KeyLoop.Record=>a.2.2) hh).symm
  · have hge : ((KeyLoop.indexed 0 xs).map some).length ≤ i := by simpa using Nat.le_of_not_gt hi
    rw [List.getElem?_append_right hge] at he
    simp only [List.getElem?_replicate] at he
    split at he <;> simp at he

theorem packet_position (r : Request) (g : Fin r.Gates) (i : ℕ) (e : KeyLoop.Record)
    (he : (CompetitorSameBucketPackets.records r g)[i]?=some (some e)) : e.2.2=i :=
  indexed_rank_position _ _ i e he

end NearCubicWires.RepairOrdinary.CompetitorSameBucketRankMeaning

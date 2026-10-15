import Proof.Hierarchy.CompetitorSameBucketEntries

/-! Each source occurrence ID appears once in the ranked packet. The actual
within-bucket pair enumeration therefore emits at most one contribution for
any fixed row/column and gate, including all padding and comparator branches. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
open MatrixScoreBatch CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def hasID (id : ℕ) : Option KeyLoop.Record → Bool
  | none => false
  | some e => decide (e.2.1=id)
def inCell (row col : ℕ) (e : Entry) := decide (e.row=row ∧ e.rightTaggedID=col)

theorem indexed_map_ids (n : ℕ) (xs : List (ℤ×ℕ)) :
    (KeyLoop.indexed n xs).map (fun e=>e.2.1)=xs.map Prod.snd := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨score,id⟩;simp [KeyLoop.indexed,ih]

theorem ranked_ids_nodup (r : Request) (g : Fin r.Gates) :
    ((MatrixScoreRawRanks.entries r g).map (fun e=>e.2.1)).Nodup := by
  rw [MatrixScoreRawRanks.entries,indexed_map_ids]
  simp only [KeyLoop.dominanceEntries,List.map_map]
  have hs:=DominanceSort.sorted_semantics r.S r.M (leftScore r) (rightScore r) g
    (MatrixScoreRawRanks.size_fit r) (score_lo r g) (score_hi r g)
  have hn : (DominanceSort.copies r.U r.U).Nodup :=
    List.nodup_ofFn.mpr finSumFinEquiv.symm.injective
  apply (hs.1.nodup_iff.mpr hn).map
  intro a b h
  apply finSumFinEquiv.injective
  exact Fin.ext h

theorem packet_id_count (r : Request) (g : Fin r.Gates) (id : ℕ) :
    (CompetitorSameBucketPackets.records r g).countP (hasID id) ≤ 1 := by
  have h := List.nodup_iff_count_le_one.mp (ranked_ids_nodup r g) id
  simpa [CompetitorSameBucketPackets.records,List.countP_map,List.countP_replicate,
    List.count_eq_countP,hasID,Function.comp_def,Bool.beq_eq_decide_eq] using h

theorem flatMap_count_bound {α β : Type} (xs : List α) (f : α → List β)
    (p : α → Bool) (q : β → Bool) (k : ℕ)
    (hf : ∀ x∈xs,(f x).countP q ≤ if p x then k else 0) :
    (xs.flatMap f).countP q ≤ xs.countP p*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=hf x (by simp)
    have ht:=ih (by intro y hy;exact hf y (by simp [hy]))
    simp only [List.flatMap_cons,List.countP_append,List.countP_cons]
    cases hp : p x <;> simp only [hp,Bool.false_eq_true,↓reduceIte] at hx ⊢ <;> nlinarith

theorem pair_cell_count (r : Request) (c : ℤ) (row col : ℕ) (a b : Option KeyLoop.Record) :
    (pair r c a b).countP (inCell row col) ≤
      if hasID row a then (if hasID col b then 1 else 0) else 0 := by
  cases a with
  | none => simp [pair,hasID]
  | some a =>
    cases b with
    | none => simp [pair,hasID]
    | some b =>
      simp only [pair,hasID]
      split
      · by_cases ha : a.2.1=row <;> by_cases hb : b.2.1=col <;> simp [inCell,ha,hb]
      · simp

theorem row_cell_count (r : Request) (c : ℤ) (row col : ℕ) (xs : List (Option KeyLoop.Record)) :
    (xs.flatMap (fun a=>xs.flatMap (fun b=>pair r c a b))).countP (inCell row col) ≤
      xs.countP (hasID row)*xs.countP (hasID col) := by
  apply flatMap_count_bound
  intro a _
  cases ha : hasID row a
  · have h:=flatMap_count_bound xs (fun b=>pair r c a b) (hasID col) (inCell row col) 0 (by
      intro b _
      have hb:=pair_cell_count r c row col a b
      simpa only [ha,Bool.false_eq_true,↓reduceIte,ite_self] using hb)
    simpa only [ha,Bool.false_eq_true,↓reduceIte,Nat.mul_zero] using h
  · have h:=flatMap_count_bound xs (fun b=>pair r c a b) (hasID col) (inCell row col) 1 (by
      intro b _
      simpa only [ha,↓reduceIte] using pair_cell_count r c row col a b)
    simpa only [ha,↓reduceIte,Nat.mul_one] using h

theorem rows_cell_count (r : Request) (c : ℤ) (row col : ℕ) (xss : List (List (Option KeyLoop.Record))) :
    (xss.flatMap (fun xs=>xs.flatMap (fun a=>xs.flatMap (fun b=>pair r c a b)))).countP (inCell row col) ≤
      xss.flatten.countP (hasID row)*xss.flatten.countP (hasID col) := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
    have hx:=row_cell_count r c row col xs
    simp only [List.flatMap_cons,List.countP_append,List.flatten_cons]
    nlinarith

theorem gate_cell_count (r : Request) (g : Fin r.Gates) (row col : ℕ) :
    (atCell row col (gate r g)).length ≤ 1 := by
  have h:=rows_cell_count r (weight r g) row col (CompetitorSameBucketPacketRows.rows r g)
  rw [CompetitorSameBucketPacketRows.rows_flatten] at h
  have hl:=packet_id_count r g row
  have hr:=packet_id_count r g col
  change (gate r g).countP (inCell row col) ≤ _ at h
  rw [List.countP_eq_length_filter] at h
  exact h.trans ((Nat.mul_le_mul hl hr).trans (by decide))

end NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries

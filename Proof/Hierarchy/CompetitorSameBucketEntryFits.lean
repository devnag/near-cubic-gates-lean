import Proof.Hierarchy.CompetitorSameBucketEntryCounts

/-! Source-derived same-bucket P/N bounds at the existing width b+2p+2.
The proof counts each gate once per cell, and transfers totals through the
actual sort permutation. No table-width enlargement or supplied fit premise. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
open MatrixScoreBatch CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem parts_bound (es : List Entry) (k : ℕ) (h : ∀ e∈es,e.coefficient.natAbs ≤ k) :
    positive es+negative es ≤ es.length*k := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he:=h e (by simp)
    have ht:=ih (by intro a ha;exact h a (by simp [ha]))
    have hp:=Int.toNat_add_toNat_neg_eq_natAbs e.coefficient
    simp only [positive_cons,negative_cons,List.length_cons]
    nlinarith

theorem gate_bits (r : Request) (g : Fin r.Gates) :
    ∀ e∈gate r g,e.coefficient.natAbs < 2^r.p := by
  intro e he
  apply entries_bits r e
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨g,by simp,he⟩

theorem gate_parts_bound (r : Request) (g : Fin r.Gates) (row col : ℕ) :
    positive (atCell row col (gate r g))+negative (atCell row col (gate r g)) ≤ 2^r.p := by
  have h:=parts_bound (atCell row col (gate r g)) (2^r.p) (by
    intro e he
    exact (gate_bits r g e (List.mem_filter.mp he).1).le)
  exact h.trans ((Nat.mul_le_mul_right (2^r.p) (gate_cell_count r g row col)).trans (by simp))

theorem atCell_append (row col : ℕ) (xs ys : List Entry) :
    atCell row col (xs++ys)=atCell row col xs++atCell row col ys := List.filter_append xs ys

theorem flatMap_parts_bound {α : Type} (xs : List α) (f : α → List Entry) (row col k : ℕ)
    (h : ∀ x∈xs,positive (atCell row col (f x))+negative (atCell row col (f x)) ≤ k) :
    positive (atCell row col (xs.flatMap f))+negative (atCell row col (xs.flatMap f)) ≤ xs.length*k := by
  induction xs with
  | nil => simp [atCell]
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (by intro a ha;exact h a (by simp [ha]))
    simp only [List.flatMap_cons,atCell_append,positive_append,negative_append,List.length_cons]
    nlinarith

theorem zeros_parts (u row col : ℕ) :
    positive (atCell row col (zeros u))+negative (atCell row col (zeros u))=0 := by
  have h:=parts_bound (atCell row col (zeros u)) 0 (by
    intro e he
    have he:=(List.mem_filter.mp he).1
    simp only [zeros,List.mem_flatMap,List.mem_map] at he
    obtain ⟨i,_,j,_,rfl⟩:=he
    simp)
  omega

theorem cell_parts_bound (r : Request) (row col : ℕ) :
    positive (atCell row col (entries r))+negative (atCell row col (entries r)) ≤ r.Gates*2^r.p := by
  have h:=flatMap_parts_bound (List.finRange r.Gates) (gate r) row col (2^r.p)
    (by intro g _;exact gate_parts_bound r g row col)
  simp only [List.length_finRange] at h
  have hz:=zeros_parts r.U row col
  simp only [entries,atCell_append,positive_append,negative_append]
  change positive (atCell row col (contributions r))+negative (atCell row col (contributions r)) ≤ _ at h
  omega

theorem parts_perm (row col : ℕ) (xs ys : List Entry) (h : xs.Perm ys) :
    positive (atCell row col xs)=positive (atCell row col ys) ∧
    negative (atCell row col xs)=negative (atCell row col ys) := by
  have hf:=h.filter (fun e=>decide (e.row=row ∧ e.rightTaggedID=col))
  constructor
  · exact (hf.map (fun e : Entry=>e.coefficient.toNat)).sum_eq
  · exact (hf.map (fun e : Entry=>(-e.coefficient).toNat)).sum_eq

theorem cell_fit (r : Request) (row col : ℕ) :
    positive (atCell row col (entries r)) < 2^CompetitorPlaneWidth.width (natBitLength r.U) r.p ∧
    negative (atCell row col (entries r)) < 2^CompetitorPlaneWidth.width (natBitLength r.U) r.p := by
  have hg : r.Gates ≤ r.U :=
    (Nat.le_mul_self r.Gates).trans (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hu : r.U < 2^natBitLength r.U := Nat.lt_pow_succ_log_self (by decide) r.U
  have hp:=Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos r.p)
  have he : 2^natBitLength r.U*2^r.p ≤ 2^CompetitorPlaneWidth.width (natBitLength r.U) r.p := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by unfold CompetitorPlaneWidth.width;omega)
  have hc:=cell_parts_bound r row col
  have hb:=Nat.mul_le_mul_right (2^r.p) hg
  exact ⟨(Nat.le_add_right _ _).trans_lt (hc.trans hb |>.trans_lt (hp.trans_le he)),
    (Nat.le_add_left _ _).trans_lt (hc.trans hb |>.trans_lt (hp.trans_le he))⟩

theorem sorted_fit (r : Request) (es : List Entry) (h : es.Perm (entries r)) :
    ∀ row col : Fin r.U,
      positive (atCell row.val (r.U+col.val) es) < 2^CompetitorPlaneWidth.width (natBitLength r.U) r.p ∧
      negative (atCell row.val (r.U+col.val) es) < 2^CompetitorPlaneWidth.width (natBitLength r.U) r.p := by
  intro row col
  obtain ⟨hp,hn⟩:=parts_perm row.val (r.U+col.val) es (entries r) h
  rw [hp,hn]
  exact cell_fit r _ _

theorem dense_perm (w u : ℕ) (xs ys : List Entry) (h : xs.Perm ys) : dense w u xs=dense w u ys := by
  have hc : cells u xs=cells u ys := by
    unfold cells
    congr 1
    funext row
    congr 1
    funext col
    obtain ⟨hp,hn⟩:=parts_perm row.val (u+col.val) xs ys h
    simp only [cell,hp,hn]
  exact congrArg (CompetitorPlaneStream.oldWords w) hc

end NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries

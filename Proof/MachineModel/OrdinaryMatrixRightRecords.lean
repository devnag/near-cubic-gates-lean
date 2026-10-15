import Proof.MachineModel.OrdinaryMatrixBatchRightPass
import Proof.MachineModel.OrdinaryMatrixRightHandoff
import Proof.MachineModel.OrdinaryMatrixRightPaper

/-! The executed right stream is exactly the right-plane consumer's full
occurrence order: gates, buckets, then stable sorted ids. Zero cells and
zero gates are included literally in the same serialized stream. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightRecords
open LocalBitMultitape MatrixScoreBatch SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bucket (r : Request) (g : Fin r.Gates) (a inner : ℕ) :=
  (MatrixScoreRawRanks.entries r g).map (fun e => (decide (a≤e.2.2),inner,e.2.1))
noncomputable def gate (r : Request) (g : Fin r.Gates) :=
  (List.finRange r.Buckets).flatMap (fun b => bucket r g ((b.val+1)*(r.bucketSize+1)) (g.val*r.Buckets+b.val))
noncomputable def generated (r : Request) := (List.finRange r.Gates).flatMap (gate r)
noncomputable def payload (r : Request) := MatrixRightPaper.payload r.bucketSize (leftScore r) (rightScore r)
noncomputable def order (r : Request) := CrossGrid.order r.S r.M r.bucketSize (leftScore r) (rightScore r)
noncomputable def records (r : Request) := MatrixRightInputs.original (payload r) (order r)

theorem bucket_copies (r : Request) (g : Fin r.Gates) (a inner : ℕ) :
    bucket r g a inner=(DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g).map
      (fun copy => (decide (a≤(stableDominanceRank (leftScore r) (rightScore r) g copy).val),inner,
        (stableDominanceCopyId copy).val)) := by
  unfold bucket MatrixScoreRawRanks.entries KeyLoop.dominanceEntries
  apply List.ext_getElem
  · simp
  · intro i hl hr
    have hi : i<(DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g).length := by simpa using hr
    have he : i<(KeyLoop.dominanceEntries r.S r.M (leftScore r) (rightScore r) g).length := by
      simpa [KeyLoop.dominanceEntries] using hi
    have hrank := DominanceSort.sorted_rank r.S r.M (leftScore r) (rightScore r) g
      (MatrixScoreRawRanks.size_fit r) (score_lo r g) (score_hi r g) ⟨i,hi⟩
    change (stableDominanceRank (leftScore r) (rightScore r) g
      ((DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g)[i]'hi)).val=i at hrank
    have hentry := CoordinateKey.indexed_get 0 (KeyLoop.dominanceEntries r.S r.M (leftScore r) (rightScore r) g) i he
    unfold KeyLoop.dominanceEntries at hentry
    simp only [List.getElem_map]
    rw [hentry]
    simp only [Nat.zero_add,List.getElem_map]
    rw [hrank]

theorem bucket_ids (r : Request) (g : Fin r.Gates) (a inner : ℕ) :
    bucket r g a inner=((DominanceSort.sortedCopies r.S r.M (leftScore r) (rightScore r) g).map stableDominanceCopyId).map
      (fun id => (decide (a≤(stableDominanceRank (leftScore r) (rightScore r) g (finSumFinEquiv.symm id)).val),inner,id.val)) := by
  rw [bucket_copies,List.map_map]
  apply List.map_congr_left
  intro copy _
  simp [stableDominanceCopyId]

theorem generated_records (r : Request) : generated r=records r := by
  unfold generated gate records MatrixRightInputs.original
  rw [MatrixBucketCrossGrid.flatMap_product]
  apply List.flatMap_congr
  intro g _
  apply List.flatMap_congr
  intro b _
  rw [bucket_ids]
  simp only [payload,order,MatrixRightPaper.payload,CrossGrid.order,Equiv.symm_apply_apply,
    CoordinateKey.coordinate_index]
  rfl

theorem loop_fin (p : MatrixRightBucket.Params) (a inner n : ℕ) :
    MatrixRightLoop.output p a inner n=(List.finRange n).flatMap (fun b =>
      MatrixRightBucket.output p (a+b.val*p.B) (inner+b.val)) := by
  induction n generalizing a inner with
  | zero => rfl
  | succ n ih =>
    simp only [MatrixRightLoop.output,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
      Fin.val_zero,Nat.add_zero,Nat.zero_mul,ih]
    congr 1
    apply List.flatMap_congr
    intro b _
    have hi : inner+1+b.val=inner+(b.val+1) := by omega
    have ha : a+p.B+b.val*p.B=a+(b.val+1)*p.B := by ring
    simp only [Fin.val_succ,hi,ha]

theorem output_stream (r : Request) : MatrixRightGateNativeLoop.output r=
    MatrixCoordinateTranspose.stream r.M (records r) := by
  rw [← generated_records]
  unfold MatrixRightGateNativeLoop.output MatrixRightGateLoop.output generated MatrixCoordinateTranspose.stream
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro g _
  unfold MatrixRightNativeCall.output gate
  rw [loop_fin,List.flatMap_assoc]
  apply List.flatMap_congr
  intro b _
  have ha : r.bucketSize+1+b.val*(r.bucketSize+1)=(b.val+1)*(r.bucketSize+1) := by ring
  simp [MatrixRightBucket.output,MatrixRightNativeCall.params,bucket,List.flatMap_map,
    MatrixCoordinateTranspose.word,ha]

theorem order_perm (r : Request) : ∀ inner,(order r inner).Perm (List.finRange (r.U+r.U)) := by
  intro inner
  exact CoordinateKey.dominance_ids_perm r.S r.M (leftScore r) (rightScore r)
    (finProdFinEquiv.symm inner).1 (MatrixScoreRawRanks.size_fit r) (score_lo r _) (score_hi r _)

theorem records_length (r : Request) : (records r).length=r.Used*(2*r.U) := by
  have hl : ∀ inner : Fin (r.Gates*stableDominanceBucketCount r.U r.U r.bucketSize),
      (order r inner).length=2*r.U := by
    intro inner
    rw [(order_perm r inner).length_eq,List.length_finRange]
    omega
  calc
    (records r).length=(r.Gates*stableDominanceBucketCount r.U r.U r.bucketSize)*(2*r.U) := by
      simp [records,MatrixRightInputs.original,List.length_flatMap,hl]
    _ = r.Used*(2*r.U) := rfl

end NearCubicWires.RepairOrdinary.MatrixRightRecords

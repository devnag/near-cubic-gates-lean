import Proof.MachineModel.OrdinaryMatrixBatchCoordinateSort

/-! The physically traversed gate/bucket order is exactly the paper's
complete cross-grid column family, using a constant true coefficient mask. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketCrossGrid
open MatrixScoreBatch MatrixBucketKeyRecords
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem buckets_fin (K I inner a b count : ℕ) (mask : Bool) (source : List KeyLoop.Record) :
    buckets K I inner a b mask source count=(List.finRange count).flatMap (fun bucket =>
      CoordinateKey.generated K I (inner+bucket.val) (a+bucket.val*b) b mask source) := by
  induction count generalizing inner a with
  | zero => rfl
  | succ count ih =>
    simp only [buckets,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
      Fin.val_zero,Nat.add_zero,Nat.zero_mul,ih]
    congr 1
    apply List.flatMap_congr
    intro bucket _
    have hi : inner+1+bucket.val=inner+(bucket.val+1) := by omega
    have ha : a+b+bucket.val*b=a+(bucket.val+1)*b := by ring
    simp only [Fin.val_succ,hi,ha]

theorem flatMap_product {α : Type} (G B : ℕ) (f : Fin (G*B) → List α) :
    (List.finRange (G*B)).flatMap f=(List.finRange G).flatMap (fun g =>
      (List.finRange B).flatMap (fun b => f (finProdFinEquiv (g,b)))) := by
  simp only [List.flatMap_def,← List.ofFn_eq_map]
  rw [List.ofFn_mul,List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext g
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  apply congrArg f
  apply Fin.ext
  exact (CoordinateKey.coordinate_index g b).symm

noncomputable def payload (r : Request) := CrossGrid.payload r.bucketSize (leftScore r) (rightScore r)
  (fun _ => 1) false 0

theorem records_inputs (r : Request) : records r=CrossGrid.inputs r.S r.M r.M r.bucketSize
    (leftScore r) (rightScore r) (fun _ => 1) false 0 := by
  unfold CrossGrid.inputs
  rw [flatMap_product]
  unfold records
  apply List.flatMap_congr
  intro g _
  rw [gate,buckets_fin]
  apply List.flatMap_congr
  intro b _
  simp only [Equiv.symm_apply_apply,CoordinateKey.coordinate_index,Nat.zero_add]
  rfl

theorem sorted_grid (r : Request) : SortCarrier.sorted (request r)=CoordinateKey.grid r.M r.M (payload r) := by
  apply CrossGrid.sorted_inputs r.S r.M r.M r.bucketSize (leftScore r) (rightScore r)
    (fun _ => 1) false 0 (MatrixScoreRawRanks.size_fit r) _
    (score_lo r) (score_hi r) (request r) (records_inputs r)
  exact (MatrixScoreBatch.capacity r).trans ((WilliamsPaddedRequest.inner_le r.U).trans
    ((Nat.le_add_right r.U r.U).trans (MatrixScoreRawRanks.size_fit r)))

end NearCubicWires.RepairOrdinary.MatrixBucketCrossGrid

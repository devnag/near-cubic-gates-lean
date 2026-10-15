import Proof.MachineModel.OrdinaryMatrixBatchBucketPassBounds

/-! The complete physically emitted key stream is the canonical framing of
this literal record list. The next ordinary coordinate sorter consumes this
exact list with its width/count derived from the original raw Request. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketKeyRecords
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def buckets (K I inner a b : ℕ) (mask : Bool) (source : List KeyLoop.Record) : ℕ → List StablePartition.Record
  | 0 => []
  | count+1 => CoordinateKey.generated K I inner a b mask source++buckets K I (inner+1) (a+b) b mask source count
noncomputable def gate (r : Request) (g : Fin r.Gates) :=
  buckets r.M r.M (g.val*r.Buckets) 0 (r.bucketSize+1) true (MatrixScoreRawRanks.entries r g) r.Buckets
noncomputable def records (r : Request) := (List.finRange r.Gates).flatMap (gate r)

theorem bucket_bits (K I inner a b count : ℕ) (mask : Bool) (source : List KeyLoop.Record) :
    KeyBucketLoop.output K I inner a b mask source count=StablePartition.recordsBits (buckets K I inner a b mask source count) := by
  induction count generalizing inner a with
  | zero => rfl
  | succ count ih =>
    simp only [KeyBucketLoop.output,buckets,CoordinateKey.output_records,ih,StablePartition.recordsBits,List.flatMap_append]

theorem bucket_width (K I inner a b count : ℕ) (mask : Bool) (source : List KeyLoop.Record) :
    ∀ key∈buckets K I inner a b mask source count,(RadixSemantics.word key).length=I+K+1 := by
  induction count generalizing inner a with
  | zero => simp [buckets]
  | succ count ih =>
    intro key hk
    rcases List.mem_append.mp hk with hk|hk
    · obtain ⟨entry,_,rfl⟩ := List.mem_map.mp hk
      exact CoordinateKey.key_width _ _ _ _ _
    · exact ih _ _ key hk

theorem bucket_count (K I inner a b count : ℕ) (mask : Bool) (source : List KeyLoop.Record) :
    (buckets K I inner a b mask source count).length=count*source.length := by
  induction count generalizing inner a with
  | zero => simp [buckets]
  | succ count ih => simp [buckets,CoordinateKey.generated,ih,Nat.add_mul,Nat.add_comm]

theorem output_bits (r : Request) :
    MatrixBucketGateNativeLoop.output r=StablePartition.recordsBits (records r) := by
  unfold MatrixBucketGateNativeLoop.output MatrixBucketGateLoop.output records
  simp only [StablePartition.recordsBits,List.flatMap_assoc]
  apply List.flatMap_congr
  intro g _
  exact bucket_bits r.M r.M (g.val*r.Buckets) 0 (r.bucketSize+1) r.Buckets true (MatrixScoreRawRanks.entries r g)

theorem width (r : Request) : ∀ key∈records r,(RadixSemantics.word key).length=r.M+r.M+1 := by
  intro key hk
  obtain ⟨g,_,hk⟩ := List.mem_flatMap.mp hk
  exact bucket_width r.M r.M _ _ _ _ true _ key hk

theorem count (r : Request) : (records r).length=r.Used*(r.U+r.U) := by
  have hgate : ∀ g : Fin r.Gates,(gate r g).length=r.Buckets*(r.U+r.U) := by
    intro g
    rw [gate,bucket_count,MatrixBucketCallBounds.entries_length]
  unfold records
  rw [List.length_flatMap]
  have he : (List.finRange r.Gates).map (fun g => (gate r g).length)=
      List.replicate r.Gates (r.Buckets*(r.U+r.U)) := by
    simp [hgate]
  rw [he,List.sum_replicate]
  unfold Request.Used
  ring

noncomputable def request (r : Request) : SortCarrier.Request :=
  DominanceSort.fixedRequest (records r) (r.M+r.M+1) (width r)

theorem width_le (r : Request) : SortPreparation.width (records r)≤r.M+r.M+1 := by
  cases he : records r with
  | nil => simp [SortPreparation.width,SortPreparation.firstWord]
  | cons key keys =>
    have h := width r key (by simp [he])
    simpa only [SortPreparation.width,SortPreparation.firstWord,he] using h.le

theorem input_stream (r : Request) :
    MatrixBatchBucketPass.output r=ZeroPadding.pad (MatrixScoreReusableRanks.D r) (StablePartition.stream (request r).records) := by
  unfold MatrixBatchBucketPass.output
  rw [output_bits]
  rfl

end NearCubicWires.RepairOrdinary.MatrixBucketKeyRecords

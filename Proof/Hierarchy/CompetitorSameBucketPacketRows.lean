import Proof.Hierarchy.CompetitorSameBucketBucketLoop

/-! Fixed-size bucket rows are a proof view of the existing padded packet.
No new encoding or physical field is introduced. Real ranked records have
their actual bounded IDs/ranks; padding records are the existing false cells. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPacketRows
open LocalBitMultitape MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request dimension_positive)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def chunks {α : Type} (b : ℕ) : ℕ → List α → List (List α)
  | 0,_ => []
  | n+1,xs => xs.take b :: chunks b n (xs.drop b)
theorem chunks_length {α : Type} (b n : ℕ) (xs : List α) : (chunks b n xs).length=n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [chunks,ih]
theorem chunks_sizes {α : Type} (b n : ℕ) (xs : List α) (hx : xs.length=n*b) :
    ∀ ys∈chunks b n xs,ys.length=b := by
  induction n generalizing xs with
  | zero => simp [chunks]
  | succ n ih =>
    have hsize : b≤xs.length := by rw [hx]; nlinarith
    have hdrop : (xs.drop b).length=n*b := by rw [List.length_drop,hx,Nat.succ_mul]; omega
    intro ys hy
    simp only [chunks,List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp [List.length_take,hsize]
    · exact ih _ hdrop _ hy
theorem chunks_flatten {α : Type} (b n : ℕ) (xs : List α) (hx : xs.length=n*b) :
    (chunks b n xs).flatten=xs := by
  induction n generalizing xs with
  | zero => have he : xs=[] := List.length_eq_zero_iff.mp (by simpa using hx); subst xs; rfl
  | succ n ih =>
    have hdrop : (xs.drop b).length=n*b := by rw [List.length_drop,hx,Nat.succ_mul]; omega
    simpa only [chunks,List.flatten_cons,ih _ hdrop] using List.take_append_drop b xs

noncomputable def rows (r : Request) (gate : Fin r.Gates) :=
  chunks (r.bucketSize+1) r.Buckets (CompetitorSameBucketPackets.records r gate)
theorem rows_length (r : Request) (gate : Fin r.Gates) : (rows r gate).length=r.Buckets := chunks_length ..
theorem rows_size (r : Request) (gate : Fin r.Gates) : ∀ xs∈rows r gate,xs.length=r.bucketSize+1 :=
  chunks_sizes _ _ _ (CompetitorSameBucketPackets.records_length r gate)
theorem rows_flatten (r : Request) (gate : Fin r.Gates) : (rows r gate).flatten=CompetitorSameBucketPackets.records r gate :=
  chunks_flatten _ _ _ (CompetitorSameBucketPackets.records_length r gate)
theorem packet_eq (r : Request) (gate : Fin r.Gates) :
    CompetitorSameBucketBucketLoop.packet r (rows r gate)=
      CompetitorSameBucketCandidate.words r (CompetitorSameBucketPackets.records r gate) := by
  unfold CompetitorSameBucketBucketLoop.packet CompetitorSameBucketCandidate.words
  rw [←rows_flatten r gate]
  induction rows r gate with
  | nil => rfl
  | cons xs xss ih => simp [List.flatMap_cons,List.flatten_cons,List.flatMap_append,ih]

theorem indexed_ids (n bound : ℕ) (xs : List (ℤ×ℕ)) (h : ∀ x∈xs,x.2<bound) :
    ∀ e∈KeyLoop.indexed n xs,e.2.1<bound := by
  induction xs generalizing n with
  | nil => simp [KeyLoop.indexed]
  | cons x xs ih =>
    rcases x with ⟨score,id⟩
    intro e he
    simp only [KeyLoop.indexed,List.mem_cons] at he
    rcases he with rfl | he
    · exact h (score,id) (by simp)
    · exact ih (n+1) (fun y hy => h y (by simp [hy])) e he

theorem entries_fit (r : Request) (gate : Fin r.Gates) :
    ∀ e∈MatrixScoreRawRanks.entries r gate,CompetitorSameBucketCandidate.Fits r (some e) := by
  let xs := KeyLoop.dominanceEntries r.S r.M (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r) gate
  have hids : ∀ e∈xs,e.2<2^r.M := by
    intro e he
    obtain ⟨copy,_,rfl⟩ := List.mem_map.mp he
    exact (SupplierPrinter.stableDominanceCopyId copy).isLt.trans_le (MatrixScoreRawRanks.size_fit r)
  have hlen : xs.length=r.U+r.U := by
    have h := MatrixBucketCallBounds.entries_length r gate
    simpa only [MatrixScoreRawRanks.entries,KeyLoop.indexed_length] using h
  have hp : r.U+r.U<2^(r.M+r.S+1) := by
    have hm : r.M<r.M+r.S+1 := by omega
    exact (MatrixScoreRawRanks.size_fit r).trans_lt (Nat.pow_lt_pow_right (by decide) hm)
  have hir := KeyLoop.indexed_fits (r.M+r.S+1) 0 xs (by simpa only [Nat.zero_add,hlen] using hp)
  intro e he v hv
  cases Option.some.inj hv
  exact ⟨indexed_ids 0 (2^r.M) xs hids e he,hir e he⟩

theorem records_fit (r : Request) (gate : Fin r.Gates) :
    ∀ e∈CompetitorSameBucketPackets.records r gate,CompetitorSameBucketCandidate.Fits r e := by
  intro e he
  simp only [CompetitorSameBucketPackets.records,List.mem_append,List.mem_map,List.mem_replicate] at he
  rcases he with ⟨a,ha,rfl⟩ | ⟨_,rfl⟩
  · exact entries_fit r gate a ha
  · intro v hv; contradiction

theorem rows_fit (r : Request) (gate : Fin r.Gates) :
    ∀ xs∈rows r gate,∀ e∈xs,CompetitorSameBucketCandidate.Fits r e := by
  intro xs hx e he
  apply records_fit r gate e
  rw [←rows_flatten r gate]
  exact List.mem_flatten.mpr ⟨xs,hx,he⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPacketRows

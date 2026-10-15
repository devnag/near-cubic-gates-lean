import Proof.MachineModel.OrdinaryCompare

/-! Exact bucket predicates as rank-boundary comparisons. This retains the
existing bucket size and layout; no alternative partition is introduced.
The right cross-matrix cell is produced by an actual bounded-word scan. -/
namespace NearCubicWires.RepairOrdinary.BucketBoundary
open LocalBitMultitape SupplierPrinter SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem later (rank bucketSize bucket : ℕ) :
    bucket < rank / (bucketSize + 1) ↔ (bucket + 1) * (bucketSize + 1) ≤ rank := by
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le (Nat.succ_pos _)]

theorem same (rank bucketSize bucket : ℕ) :
    rank / (bucketSize + 1) = bucket ↔
      bucket * (bucketSize + 1) ≤ rank ∧ ¬(bucket + 1) * (bucketSize + 1) ≤ rank := by
  have hlo : bucket ≤ rank / (bucketSize + 1) ↔ bucket * (bucketSize + 1) ≤ rank :=
    Nat.le_div_iff_mul_le (Nat.succ_pos _)
  have hhi := later rank bucketSize bucket
  omega

theorem right_cell {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (bucketSize : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize)) (column : Fin Columns) :
    laterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize) (gate, bucket) column =
      decide ((bucket.val + 1) * (bucketSize + 1) ≤
        (stableDominanceRank leftScore rightScore gate (.inr column)).val) := by
  simp only [laterBucketRight, stableBucketedDominanceLayout, Fin.lt_def, stableDominanceBucket, later]

theorem left_cell {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (bucketSize : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize)) (row : Fin Rows) :
    laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize) weight row (gate, bucket) =
      if bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val ∧
        ¬(bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val
      then weight gate else 0 := by
  have he : bucket = (stableBucketedDominanceLayout leftScore rightScore bucketSize).leftBucket row gate ↔
      bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val ∧
        ¬(bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val := by
    rw [Fin.ext_iff]
    change bucket.val = (stableDominanceRank leftScore rightScore gate (.inl row)).val / (bucketSize + 1) ↔ _
    rw [eq_comm, same]
  simp only [laterBucketLeft, he]

theorem right_cell_run {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (bucketSize width : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize)) (column : Fin Columns)
    (hrank : Rows + Columns ≤ 2 ^ width) (hboundary : (bucket.val + 1) * (bucketSize + 1) < 2 ^ width) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom Compare.machine (2 * width + 1)
        (Compare.config (Compare.scanState true)
          (frame (binary width ((bucket.val + 1) * (bucketSize + 1))))
          (frame (binary width (stableDominanceRank leftScore rightScore gate (.inr column)).val)) 0 0 []) = some r ∧
      r.final.tapes 2 =
        [laterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize) (gate, bucket) column] ∧
      r.final.heads 0 = 2 * width ∧ r.final.heads 1 = 2 * width ∧
      r.steps = 2 * width + 1 ∧ r.peakTapeCells ≤ 4 * width + 3 := by
  let rank := (stableDominanceRank leftScore rightScore gate (.inr column)).val
  let boundary := (bucket.val + 1) * (bucketSize + 1)
  have hfit : rank < 2 ^ width := (stableDominanceRank leftScore rightScore gate (.inr column)).isLt.trans_le hrank
  obtain ⟨r, hr, hf, hs, hp⟩ := Compare.compare_run [] [] (binary width boundary) (binary width rank) [] [] []
    (by simp)
  refine ⟨r, by simpa only [List.nil_append, List.append_nil, List.length_nil, binary_length] using hr,
    ?_, ?_, ?_, by simpa using hs, ?_⟩
  · rw [right_cell]
    have hb : boundary < 2 ^ width := hboundary
    simp [hf, Compare.config, binary_value _ _ hb, binary_value _ _ hfit]
    rfl
  · simp [hf, Compare.config]
  · simp [hf, Compare.config]
  · simp only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, frame_length, binary_length] at hp
    omega

end NearCubicWires.RepairOrdinary.BucketBoundary

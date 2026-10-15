import Proof.MachineModel.OrdinaryBucketBoundary

/-! Discharge the word-width condition at the actual capacity-selected B.3
bucket. Two extra scalar bits cover every boundary, including the last empty
bucket and the one-bucket case. -/
namespace NearCubicWires.RepairOrdinary.BucketBoundary
open LocalBitMultitape SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_size_le (rows columns capacity gates : ℕ) :
    stableCapacityBucketSize rows columns capacity gates ≤ rows + columns := by
  dsimp only [stableCapacityBucketSize]
  split
  · exact Nat.le_refl _
  · exact Nat.div_le_self _ _

theorem boundary_fits {rows columns bucketSize : ℕ} (width : ℕ)
    (bucket : Fin (stableDominanceBucketCount rows columns bucketSize))
    (hsize : bucketSize ≤ rows + columns) (hrank : rows + columns ≤ 2 ^ width) :
    (bucket.val + 1) * (bucketSize + 1) < 2 ^ (width + 2) := by
  have hidx : bucket.val ≤ (rows + columns) / (bucketSize + 1) := by
    have h := bucket.isLt
    change bucket.val < (rows + columns) / (bucketSize + 1) + 1 at h
    omega
  have hm := Nat.mul_le_mul_right (bucketSize + 1) hidx
  have hd := Nat.div_mul_le_self (rows + columns) (bucketSize + 1)
  have hb : (bucket.val + 1) * (bucketSize + 1) ≤ 2 * (rows + columns) + 1 := by nlinarith
  have hp : 0 < 2 ^ width := pow_pos (by decide) _
  have he : 2 ^ (width + 2) = 4 * 2 ^ width := by rw [pow_add]; ring
  rw [he]
  omega

theorem capacity_right_cell_run {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (capacity width : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (column : Fin Columns) (hrank : Rows + Columns ≤ 2 ^ width) :
    let bucketSize := stableCapacityBucketSize Rows Columns capacity Gates
    ∃ r : ExecutionReceipt 3 5,
      runFrom Compare.machine (2 * (width + 2) + 1)
        (Compare.config (Compare.scanState true)
          (frame (binary (width + 2) ((bucket.val + 1) * (bucketSize + 1))))
          (frame (binary (width + 2) (stableDominanceRank leftScore rightScore gate (.inr column)).val)) 0 0 []) = some r ∧
      r.final.tapes 2 =
        [laterBucketRight (stableBucketedDominanceLayout leftScore rightScore bucketSize) (gate, bucket) column] ∧
      r.final.heads 0 = 2 * (width + 2) ∧ r.final.heads 1 = 2 * (width + 2) ∧
      r.steps = 2 * (width + 2) + 1 ∧ r.peakTapeCells ≤ 4 * (width + 2) + 3 := by
  have hp : 2 ^ width ≤ 2 ^ (width + 2) := by rw [pow_add]; norm_num
  exact right_cell_run leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates) (width + 2)
    gate bucket column (hrank.trans hp)
    (boundary_fits width bucket (capacity_size_le Rows Columns capacity Gates) hrank)

end NearCubicWires.RepairOrdinary.BucketBoundary

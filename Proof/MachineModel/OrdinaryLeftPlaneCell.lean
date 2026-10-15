import Proof.MachineModel.OrdinaryInterval

/-! The interval scan at the exact positive/negative coefficient bit of the
paper's left cross-bucket matrix. Boundary and coefficient-bit production
remain explicit caller operations. -/
namespace NearCubicWires.RepairOrdinary.LeftPlaneCell
open LocalBitMultitape SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficientBit (negative : Bool) (value : ℤ) (bit : ℕ) : Bool :=
  if negative then negativeMagnitudeBit value bit else positiveMagnitudeBit value bit

@[simp] theorem coefficient_zero (negative : Bool) (bit : ℕ) : coefficientBit negative 0 bit = false := by
  cases negative <;> simp [coefficientBit, negativeMagnitudeBit, positiveMagnitudeBit]

theorem left_bit {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (bucketSize : ℕ)
    (gate : Fin Gates) (bucket : Fin (stableDominanceBucketCount Rows Columns bucketSize))
    (row : Fin Rows) (negative : Bool) (bit : ℕ) :
    coefficientBit negative
        (laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize) weight row (gate, bucket)) bit =
      ((decide (bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val) &&
        !decide ((bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val)) &&
        coefficientBit negative (weight gate) bit) := by
  rw [BucketBoundary.left_cell]
  by_cases hlo : bucket.val * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val <;>
    by_cases hhi : (bucket.val + 1) * (bucketSize + 1) ≤ (stableDominanceRank leftScore rightScore gate (.inl row)).val <;>
      simp [hlo, hhi]

theorem capacity_cell_run {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (capacity width : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (row : Fin Rows) (negative : Bool) (bit : ℕ) (output : List Bool) (hrank : Rows + Columns ≤ 2 ^ width) :
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    let rank := (stableDominanceRank leftScore rightScore gate (.inl row)).val
    ∃ r : ExecutionReceipt 5 9,
      runFrom Interval.machine (2 * (width + 2) + 1)
        (Interval.config (Interval.scanState true true) (frame (binary (width + 2) (bucket.val * B)))
          (frame (binary (width + 2) rank)) (frame (binary (width + 2) ((bucket.val + 1) * B))) 0 0 0
          output (coefficientBit negative (weight gate) bit)) = some r ∧
      r.final.tapes 3 = output ++
        [coefficientBit negative (laterBucketLeft
          (stableBucketedDominanceLayout leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates))
          weight row (gate, bucket)) bit] ∧
      r.final.heads 3 = output.length + 1 ∧ r.steps = 2 * (width + 2) + 1 ∧
      r.peakTapeCells ≤ 6 * (width + 2) + output.length + 5 := by
  let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
  let rank := (stableDominanceRank leftScore rightScore gate (.inl row)).val
  have hupper : (bucket.val + 1) * B < 2 ^ (width + 2) :=
    BucketBoundary.boundary_fits width bucket (BucketBoundary.capacity_size_le Rows Columns capacity Gates) hrank
  have hlower : bucket.val * B < 2 ^ (width + 2) :=
    (Nat.mul_le_mul_right B (Nat.le_succ _)).trans_lt hupper
  have hp : 2 ^ width ≤ 2 ^ (width + 2) := by rw [pow_add]; norm_num
  have hfit : rank < 2 ^ (width + 2) :=
    (stableDominanceRank leftScore rightScore gate (.inl row)).isLt.trans_le (hrank.trans hp)
  obtain ⟨r, hr, ho, hh, hs, hpeak⟩ := Interval.interval_run (width + 2) (bucket.val * B) rank
    ((bucket.val + 1) * B) output (coefficientBit negative (weight gate) bit) hlower hfit hupper
  refine ⟨r, hr, ?_, hh, hs, hpeak⟩
  rw [left_bit]
  exact ho

end NearCubicWires.RepairOrdinary.LeftPlaneCell

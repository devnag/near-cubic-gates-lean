import Proof.MachineModel.OrdinaryRightCell

/-! The generated-boundary right-cell program at the exact capacity-selected
paper matrix. Every scalar-fit condition follows from the common rank width. -/
namespace NearCubicWires.RepairOrdinary.RightCell
open LocalBitMultitape SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_cell_run {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (capacity width : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (column : Fin Columns) (backing output : List Bool) (hrank : Rows + Columns ≤ 2 ^ width)
    (hb : backing.length ≤ 2 * (width + 2) + 1) :
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    let rank := (stableDominanceRank leftScore rightScore gate (.inr column)).val
    ∃ r : ExecutionReceipt 6 12,
      runFrom machine (6 * (width + 2) + 6)
        (Composition.leftConfig 5 (config (width + 2) (bucket.val * B) B rank backing output)) = some r ∧
      r.final.tapes 5 = output ++
        [laterBucketRight (stableBucketedDominanceLayout leftScore rightScore
          (stableCapacityBucketSize Rows Columns capacity Gates)) (gate, bucket) column] ∧
      r.final.tapes 2 = frame (binary (width + 2) ((bucket.val + 1) * B)) ∧
      r.final.tapes 1 = frame (binary (width + 2) B) ∧
      r.final.heads 5 = output.length + 1 ∧
      r.steps = 6 * (width + 2) + 6 ∧ r.peakTapeCells ≤ 14 * (width + 2) + output.length + 7 := by
  let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
  let rank := (stableDominanceRank leftScore rightScore gate (.inr column)).val
  have he : bucket.val * B + B = (bucket.val + 1) * B := by simp [Nat.add_mul]
  have hup : bucket.val * B + B < 2 ^ (width + 2) := by
    rw [he]
    exact BucketBoundary.boundary_fits width bucket
      (BucketBoundary.capacity_size_le Rows Columns capacity Gates) hrank
  have hp : 2 ^ width ≤ 2 ^ (width + 2) := by rw [pow_add]; norm_num
  have hfit : rank < 2 ^ (width + 2) :=
    (stableDominanceRank leftScore rightScore gate (.inr column)).isLt.trans_le (hrank.trans hp)
  obtain ⟨r, hr, ho, hupper, hB, hh, hs, hpeak⟩ := cell_run (width + 2) (bucket.val * B) B rank backing output hup hfit hb
  refine ⟨r, hr, ?_, by simpa only [he] using hupper, hB, hh, hs, hpeak⟩
  have hcell := BucketBoundary.right_cell leftScore rightScore
    (stableCapacityBucketSize Rows Columns capacity Gates) gate bucket column
  rw [hcell]
  simpa only [he, B, rank] using ho

end NearCubicWires.RepairOrdinary.RightCell

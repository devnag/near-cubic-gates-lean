import Proof.MachineModel.OrdinaryCellLoop

/-! A whole signed B.3 bucket-column scan at the unchanged capacity bucket.
The actual loop consumes framed canonical ranks in the supplied row order;
producing that rank stream and final coordinate ordering remain caller work. -/
namespace NearCubicWires.RepairOrdinary.CellLoop
open LocalBitMultitape SupplierPrinter SignedSortKey LeftPlaneCell
open CellLoad (config)
open RecordController (test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_scan {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (capacity width : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (rowOrder : List (Fin Rows)) (negative : Bool) (bit initialRank : ℕ) (pre backing out : List Bool)
    (hrank : Rows + Columns ≤ 2 ^ width) (hb : backing.length ≤ 2 * (width + 2) + 1) :
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    let ranks := rowOrder.map (fun row => (stableDominanceRank leftScore rightScore gate (.inl row)).val)
    let mask := coefficientBit negative (weight gate) bit
    ∃ finalRank finalBacking, finalBacking.length ≤ 2 * (width + 2) + 1 ∧
      ∃ r : ExecutionReceipt 10 26,
        runFrom machine (rowOrder.length * (16 * (width + 2) + 22) + 1)
          (config (test 24) (width + 2) (bucket.val * B) B initialRank backing mask
            (pre ++ stream (width + 2) ranks) pre.length out) = some r ∧
        r.final = config (stop 24) (width + 2) (bucket.val * B) B finalRank finalBacking mask
          (pre ++ stream (width + 2) ranks) (pre.length + (fields (width + 2) ranks).length)
          (out ++ rowOrder.map (fun row => coefficientBit negative (laterBucketLeft
            (stableBucketedDominanceLayout leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates))
            weight row (gate, bucket)) bit)) ∧
        r.steps = rowOrder.length * (16 * (width + 2) + 22) + 1 ∧
        r.peakTapeCells ≤ (pre ++ stream (width + 2) ranks).length + 26 * (width + 2) +
          out.length + rowOrder.length + 22 := by
  let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
  let ranks := rowOrder.map (fun row => (stableDominanceRank leftScore rightScore gate (.inl row)).val)
  let mask := coefficientBit negative (weight gate) bit
  have hupper : (bucket.val + 1) * B < 2 ^ (width + 2) :=
    BucketBoundary.boundary_fits width bucket (BucketBoundary.capacity_size_le Rows Columns capacity Gates) hrank
  have he : bucket.val * B + B = (bucket.val + 1) * B := by simp [Nat.add_mul]
  have hp : 2 ^ width ≤ 2 ^ (width + 2) := by rw [pow_add]; norm_num
  have hfits : ∀ rank ∈ ranks, rank < 2 ^ (width + 2) := by
    intro rank hm
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hm
    exact (stableDominanceRank leftScore rightScore gate (.inl row)).isLt.trans_le (hrank.trans hp)
  have hbits : bits (bucket.val * B) B mask ranks = rowOrder.map (fun row => coefficientBit negative
      (laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates))
        weight row (gate, bucket)) bit) := by
    simp only [bits, ranks, List.map_map]
    apply List.map_congr_left
    intro row _
    rw [left_bit]
    simp [LeftCell.selected, he, B, mask]
  obtain ⟨finalRank, finalBacking, hback, r, hr, hf, hs, hpeak⟩ := loop_run (width + 2) (bucket.val * B) B initialRank
    ranks pre backing out mask (by omega) (by rw [he]; exact hupper) hfits hb
  simp only [ranks, List.length_map] at hr hs hpeak
  rw [hbits] at hf
  exact ⟨finalRank, finalBacking, hback, r, hr, hf, hs, hpeak⟩

end NearCubicWires.RepairOrdinary.CellLoop

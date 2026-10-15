import Proof.MachineModel.OrdinaryCellEmit

/-! The reusable cell emitter at the literal signed B.3 matrix entry.
Capacity-selected bucket widths discharge every local arithmetic guard. -/
namespace NearCubicWires.RepairOrdinary.CellEmit
open LocalBitMultitape SupplierPrinter LeftPlaneCell SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_cell_run {Rows Gates Columns : ℕ} (leftScore : IntMatrix Rows Gates)
    (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ) (capacity width : ℕ) (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (row : Fin Rows) (negative : Bool) (bit : ℕ) (backing out : List Bool)
    (hrank : Rows + Columns ≤ 2 ^ width) (hb : backing.length ≤ 2 * (width + 2) + 1) :
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    let rank := (stableDominanceRank leftScore rightScore gate (.inl row)).val
    let mask := coefficientBit negative (weight gate) bit
    ∃ r : ExecutionReceipt 9 20,
      runFrom machine (12 * (width + 2) + 16)
        (config machine.start (LocalCell.input (width + 2) (bucket.val * B) B rank backing mask) out) = some r ∧
      r.final.tapes 8 = out ++ [coefficientBit negative (laterBucketLeft
        (stableBucketedDominanceLayout leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates))
        weight row (gate, bucket)) bit] ∧
      r.final.tapes 0 = frame (binary (width + 2) (bucket.val * B)) ∧
      r.final.tapes 1 = frame (binary (width + 2) B) ∧
      r.final.tapes 2 = frame (binary (width + 2) ((bucket.val + 1) * B)) ∧
      r.final.tapes 3 = List.replicate (2 * (width + 2) + 1) false ∧
      r.final.tapes 5 = [false] ∧
      r.final.tapes 7 = List.replicate (6 * (width + 2) + 6) false ∧
      (∀ i : Fin 8, r.final.heads (i.castAdd 1) = 0) ∧ r.final.heads 8 = out.length + 1 ∧
      r.steps = 12 * (width + 2) + 16 ∧ r.peakTapeCells ≤ 26 * (width + 2) + out.length + 22 := by
  let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
  let rank := (stableDominanceRank leftScore rightScore gate (.inl row)).val
  let mask := coefficientBit negative (weight gate) bit
  have hupper : (bucket.val + 1) * B < 2 ^ (width + 2) :=
    BucketBoundary.boundary_fits width bucket (BucketBoundary.capacity_size_le Rows Columns capacity Gates) hrank
  have he : bucket.val * B + B = (bucket.val + 1) * B := by simp [Nat.add_mul]
  have hp : 2 ^ width ≤ 2 ^ (width + 2) := by rw [pow_add]; norm_num
  have hfit : rank < 2 ^ (width + 2) :=
    (stableDominanceRank leftScore rightScore gate (.inl row)).isLt.trans_le (hrank.trans hp)
  obtain ⟨r, hr, hf, hs, hpeak⟩ := cell_run (width + 2) (bucket.val * B) B rank backing out mask
    (by rw [he]; exact hupper) hfit hb
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs, hpeak⟩
  · rw [hf, left_bit]
    simp [config, Fin.addCases, LeftCell.selected, he, B, rank, mask]
  · simp [hf, config, cleared, LocalCell.output, Fin.addCases, B]
  · simp [hf, config, cleared, LocalCell.output, Fin.addCases, B]
  · simp [hf, config, cleared, LocalCell.output, Fin.addCases, he, B]
  · simp [hf, config, cleared, LocalCell.output, Fin.addCases]
  · simp [hf, config, cleared, Fin.addCases]
  · simp [hf, config, cleared, LocalCell.output, Fin.addCases]
  · intro i
    simp [hf, config]
  · simp [hf, config, Fin.addCases]

end NearCubicWires.RepairOrdinary.CellEmit

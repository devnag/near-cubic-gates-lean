import Proof.MachineModel.OrdinaryCoordinateKey

/-! The keyed scan at the paper's literal dominance occurrence family. The
right/type selection and matrix padding are subsequent producer operations. -/
namespace NearCubicWires.RepairOrdinary.KeyLoop
open LocalBitMultitape SupplierPrinter SignedSortKey LeftPlaneCell
open KeyCell (config)
open RecordController (test)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def dominanceEntries {Rows Gates Columns : ℕ} (S K : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates) : List (ℤ × ℕ) :=
  (DominanceSort.sortedCopies S K leftScore rightScore gate).map
    (fun copy => (stableDominanceCopyScore leftScore rightScore gate copy, (stableDominanceCopyId copy).val))

theorem dominance_words {Rows Gates Columns : ℕ} (S K : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    words S K (dominanceEntries S K leftScore rightScore gate) =
      (DominanceLabels.request S K leftScore rightScore gate hsize).sortedWords := by
  rw [DominanceLabels.sorted_words S K leftScore rightScore gate hsize hlo hhi]
  simp only [words, dominanceEntries, List.map_map, dominanceRecord, Function.comp_def]

theorem capacity_run {Rows Gates Columns : ℕ} (S K I capacity : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (negative : Bool) (bit : ℕ) (hscore : 1 ≤ S) (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    let W := K + S + 1
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    let inner := (finProdFinEquiv (gate, bucket)).val
    let req := DominanceLabels.request S K leftScore rightScore gate hsize
    let source := RankLoop.stream (RankMeaning.annotated W 0 req.sortedWords)
    let mask := coefficientBit negative (weight gate) bit
    ∃ r : ExecutionReceipt 20 55,
      runFrom machine ((Rows + Columns) * (68 * W + 4 * (I + K) + 63) + 1)
        (config (test 53) W (bucket.val * B) B 0 [] [] [] mask source 0 [] K I inner (2 * (I + K))) = some r ∧
      r.final.tapes 8 = output K I inner (bucket.val * B) B mask
        (indexed 0 (dominanceEntries S K leftScore rightScore gate)) ∧
      r.steps ≤ (Rows + Columns) * (68 * W + 4 * (I + K) + 63) + 1 ∧
      r.peakTapeCells ≤ source.length + 104 * W + 8 * I + 6 * K +
        (Rows + Columns) * (2 * (I + K) + 3) + 2 * (I + K) + 64 := by
  let W := K + S + 1
  let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
  let inner := (finProdFinEquiv (gate, bucket)).val
  let req := DominanceLabels.request S K leftScore rightScore gate hsize
  let entries := dominanceEntries S K leftScore rightScore gate
  let source := RankLoop.stream (RankMeaning.annotated W 0 req.sortedWords)
  let mask := coefficientBit negative (weight gate) bit
  have hupper := BucketBoundary.boundary_fits K bucket
    (BucketBoundary.capacity_size_le Rows Columns capacity Gates) hsize
  have hp : 2 ^ (K + 2) ≤ 2 ^ W := by
    have he : W = (K + 2) + (S - 1) := by dsimp [W]; omega
    have hpow : 2 ^ W = 2 ^ (K + 2) * 2 ^ (S - 1) := by rw [he, pow_add]
    rw [hpow]
    have hge : 1 ≤ 2 ^ (S - 1) := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
    simpa using Nat.mul_le_mul_left (2 ^ (K + 2)) hge
  have he : bucket.val * B + B = (bucket.val + 1) * B := by simp [Nat.add_mul]
  have hfit : bucket.val * B + B < 2 ^ W := by rw [he]; exact hupper.trans_le hp
  have hn : entries.length = Rows + Columns := by
    have hh := (DominanceSort.sorted_semantics S K leftScore rightScore gate hsize hlo hhi).1.length_eq
    simpa [entries, dominanceEntries, DominanceSort.copies] using hh
  have hwords : words S K entries = req.sortedWords := dominance_words S K leftScore rightScore gate hsize hlo hhi
  have hlength : entries.length = req.sortedWords.length := by
    have hh := congrArg List.length hwords
    simpa [words] using hh
  have hwidth : req.width = W := rfl
  have hcount : 0 + entries.length < 2 ^ W := by
    rw [hlength, SortRank.sorted_length]
    simpa only [hwidth, Nat.zero_add] using req.fits
  obtain ⟨_, _, _, _, _, _, _, r, hr, hf, hs, hpeak⟩ := labelled_run S K I inner (2 * (I + K))
    (bucket.val * B) B 0 0 entries [] [] [] [] [] mask hfit hcount (by simp) (by simp) (by simp) (by omega) (by omega)
  rw [hwords] at hr hf hpeak
  have hout : r.final.tapes 8 = output K I inner (bucket.val * B) B mask (indexed 0 entries) := by
    rw [hf]
    simp [config, TapeEmbedding.config, RecordCell.config, CellEmit.config, Fin.addCases]
  refine ⟨r, by simpa only [hn, List.nil_append, List.length_nil] using hr, hout,
    by simpa only [hn] using hs, ?_⟩
  simpa only [hn, List.nil_append, List.length_nil, Nat.add_zero] using hpeak

theorem left_payload {Rows Gates Columns : ℕ} (S K capacity : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ))
    (i : Fin (DominanceSort.sortedCopies S K leftScore rightScore gate).length) (row : Fin Rows)
    (hcopy : (DominanceSort.sortedCopies S K leftScore rightScore gate).get i = .inl row) :
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    LeftCell.selected (bucket.val * B) B i.val (coefficientBit negative (weight gate) bit) =
      coefficientBit negative
        (laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates))
          weight row (gate, bucket)) bit := by
  have hrank := DominanceSort.sorted_rank S K leftScore rightScore gate hsize hlo hhi i
  rw [hcopy] at hrank
  rw [left_bit]
  simp [LeftCell.selected, Nat.add_mul, hrank]

end NearCubicWires.RepairOrdinary.KeyLoop

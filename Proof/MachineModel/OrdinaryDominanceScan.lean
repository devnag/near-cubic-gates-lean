import Proof.MachineModel.OrdinaryLabelledScan

/-! The actual annotated-record cell scan at the paper's sorted dominance
occurrences. Bits at A-occurrence positions are exactly the signed left
matrix entries; retaining/selecting their row identifiers is subsequent work. -/
namespace NearCubicWires.RepairOrdinary.LabelledScan
open LocalBitMultitape SupplierPrinter SignedSortKey LeftPlaneCell
open RecordCell (config)
open RecordController (test)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem outputs_get (a b n i : ℕ) (mask : Bool) (words : List (List Bool)) (hi : i < words.length) :
    (outputs a b mask n words).getD i false = LeftCell.selected a b (n + i) mask := by
  induction i generalizing n words with
  | zero =>
    cases words with
    | nil => simp at hi
    | cons word words => simp [outputs, List.getD]
  | succ i ih =>
    cases words with
    | nil => simp at hi
    | cons word words =>
      simpa [outputs, List.getD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (n + 1) words (by simpa using hi)

theorem capacity_dominance_scan {Rows Gates Columns : ℕ} (scoreBits idBits capacity : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (gate : Fin Gates)
    (bucket : Fin (stableDominanceBucketCount Rows Columns (stableCapacityBucketSize Rows Columns capacity Gates)))
    (negative : Bool) (bit : ℕ) (hscore : 1 ≤ scoreBits) (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ)) :
    let W := idBits + scoreBits + 1
    let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
    let req := DominanceLabels.request scoreBits idBits leftScore rightScore gate hsize
    let source := RankLoop.stream (RankMeaning.annotated W 0 req.sortedWords)
    let mask := coefficientBit negative (weight gate) bit
    ∃ r : ExecutionReceipt 16 43,
      runFrom RecordLoop.machine ((Rows + Columns) * (68 * W + 53) + 1)
        (config (test 41) W (bucket.val * B) B 0 [] [] [] mask source 0 []) = some r ∧
      r.final.tapes 8 = outputs (bucket.val * B) B mask 0 req.sortedWords ∧
      (∀ (i : Fin (DominanceSort.sortedCopies scoreBits idBits leftScore rightScore gate).length) (row : Fin Rows),
        (DominanceSort.sortedCopies scoreBits idBits leftScore rightScore gate).get i = .inl row →
        (r.final.tapes 8).getD i.val false = coefficientBit negative
          (laterBucketLeft (stableBucketedDominanceLayout leftScore rightScore (stableCapacityBucketSize Rows Columns capacity Gates))
            weight row (gate, bucket)) bit) ∧
      r.steps = (Rows + Columns) * (68 * W + 53) + 1 ∧
      r.peakTapeCells ≤ source.length + 104 * W + (Rows + Columns) + 53 := by
  let W := idBits + scoreBits + 1
  let B := stableCapacityBucketSize Rows Columns capacity Gates + 1
  let req := DominanceLabels.request scoreBits idBits leftScore rightScore gate hsize
  let source := RankLoop.stream (RankMeaning.annotated W 0 req.sortedWords)
  let mask := coefficientBit negative (weight gate) bit
  have hupper := BucketBoundary.boundary_fits idBits bucket
    (BucketBoundary.capacity_size_le Rows Columns capacity Gates) hsize
  have hp : 2 ^ (idBits + 2) ≤ 2 ^ W := by
    have he : W = (idBits + 2) + (scoreBits - 1) := by dsimp [W]; omega
    have hpow : 2 ^ W = 2 ^ (idBits + 2) * 2 ^ (scoreBits - 1) := by rw [he, pow_add]
    rw [hpow]
    have hge : 1 ≤ 2 ^ (scoreBits - 1) := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
    simpa using Nat.mul_le_mul_left (2 ^ (idBits + 2)) hge
  have he : bucket.val * B + B = (bucket.val + 1) * B := by simp [Nat.add_mul]
  have hfit : bucket.val * B + B < 2 ^ W := by rw [he]; exact hupper.trans_le hp
  have hn : req.sortedWords.length = Rows + Columns := by
    rw [SortRank.sorted_length]
    simp [req, DominanceLabels.request, DominanceSort.records, DominanceSort.copies]
  have hwidth : req.width = W := rfl
  obtain ⟨_, _, _, _, _, _, _, r, hr, hf, hs, hpeak⟩ := scan_run W (bucket.val * B) B 0 0 req.sortedWords
    [] [] [] [] [] mask (by dsimp [W]; omega) hfit (SortRank.sorted_uniform req)
      (by rw [SortRank.sorted_length]; simpa only [Nat.zero_add, hwidth] using req.fits) (by simp) (by simp) (by simp)
  have hout : r.final.tapes 8 = outputs (bucket.val * B) B mask 0 req.sortedWords := by
    rw [hf]
    simp [config, TapeEmbedding.config, CellEmit.config, Fin.addCases]
  refine ⟨r, by simpa only [hn, List.nil_append, List.length_nil] using hr, hout, ?_,
    by simpa only [hn] using hs, by simpa only [hn, List.nil_append, List.length_nil, Nat.add_zero] using hpeak⟩
  intro i row hcopy
  have hi : i.val < req.sortedWords.length := by
    rw [DominanceLabels.sorted_words scoreBits idBits leftScore rightScore gate hsize hlo hhi, List.length_map]
    exact i.isLt
  have hrank := DominanceSort.sorted_rank scoreBits idBits leftScore rightScore gate hsize hlo hhi i
  rw [hcopy] at hrank
  rw [hout, outputs_get _ _ _ _ _ _ hi, left_bit]
  simp [LeftCell.selected, he, B, mask, hrank]

end NearCubicWires.RepairOrdinary.LabelledScan

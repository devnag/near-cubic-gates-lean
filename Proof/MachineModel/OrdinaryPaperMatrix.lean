import Proof.MachineModel.OrdinarySortMatrixCost

/-! The complete actual sorting/selection consumer at the paper's B.3 family.
Its keyed source and three unary dimension templates are explicit inputs. -/
namespace NearCubicWires.RepairOrdinary.PaperMatrix
open LocalBitMultitape SupplierPrinter CoordinateKey LeftPlaneCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def request {Rows Gates Columns : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ gate copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) : SortCarrier.Request :=
  DominanceSort.fixedRequest (CrossGrid.inputs S K I bucketSize leftScore rightScore weight negative bit) (I + K + 1) (by
    intro r hr
    have hp := CrossGrid.inputs_perm_grid S K I bucketSize leftScore rightScore weight negative bit hsize hlo hhi
    have hm := hp.mem_iff.mp hr
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hm
    exact key_width _ _ _ _ _)

theorem sorted_request {Rows Gates Columns : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hinner : Gates * stableDominanceBucketCount Rows Columns bucketSize ≤ 2 ^ I)
    (hlo : ∀ gate copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    SortCarrier.sorted (request S K I bucketSize leftScore rightScore weight negative bit hsize hlo hhi) =
      grid I K (CrossGrid.payload bucketSize leftScore rightScore weight negative bit) :=
  CrossGrid.sorted_inputs S K I bucketSize leftScore rightScore weight negative bit hsize hinner hlo hhi _ rfl

theorem paper_run {Rows Gates Columns Capacity : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hinner : Gates * stableDominanceBucketCount Rows Columns bucketSize ≤ 2 ^ I)
    (hcap : Gates * stableDominanceBucketCount Rows Columns bucketSize ≤ Capacity)
    (hlo : ∀ gate copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ))
    (out : List Bool) :
    let used := Gates * stableDominanceBucketCount Rows Columns bucketSize
    let req := request S K I bucketSize leftScore rightScore weight negative bit hsize hlo hhi
    let matrix := WilliamsLoaderForms.rowMajorBitMatrix (fun row inner => coefficientBit negative
      (padSignedInner (Capacity := Capacity)
        (reindexedLaterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize) weight) row inner) bit)
    let budget := 512 * ((Rows + Columns) * used + Rows * Capacity + Rows + 1) * (I + K + 2) ^ 2
    ∃ r : ExecutionReceipt 11 136,
      runFrom SortMatrix.machine budget (SortMatrix.input req out used (Capacity - used) Rows) = some r ∧
      r.final.tapes 7 = out ++ matrix ∧ r.final.heads 7 = (out ++ matrix).length ∧ r.steps ≤ budget ∧
      r.peakTapeCells ≤ 9 * (StablePartition.stream req.records).length + 5 * SortPreparation.width req.records +
        SortCarrier.budget req.records + out.length + (Rows + 3) * Capacity + Rows + 9 := by
  dsimp only
  let req := request S K I bucketSize leftScore rightScore weight negative bit hsize hlo hhi
  let payload := CrossGrid.payload bucketSize leftScore rightScore weight negative bit
  have hgrid := sorted_request S K I bucketSize leftScore rightScore weight negative bit hsize hinner hlo hhi
  have hleft : ∀ row inner, payload (row.castAdd Columns) inner = coefficientBit negative
      (reindexedLaterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize) weight row inner) bit := by
    intro row inner
    exact CrossGrid.left_entry bucketSize leftScore rightScore weight negative bit row inner
  obtain ⟨r, hr, ho, hh, hs, hp⟩ := SortMatrix.joined_run I K payload _ negative bit hcap hleft req hgrid out
  have hb := SortMatrix.joined_budget I K payload req hgrid hcap
  let used := Gates * stableDominanceBucketCount Rows Columns bucketSize
  let small := 2 * SortCarrier.budget req.records + 3 +
    ((MatrixRows.fields (GridRows.leftRows I K payload)).length + Rows * (3 * used + 2 * (Capacity - used) + 11) + 1)
  let large := 512 * ((Rows + Columns) * used + Rows * Capacity + Rows + 1) * (I + K + 2) ^ 2
  have hmore := runFrom_moreFuel SortMatrix.machine small (large - small) _ r hr
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨r, hmore, ho, hh, hs.trans hb, hp⟩

end NearCubicWires.RepairOrdinary.PaperMatrix

import Proof.MachineModel.OrdinaryCoordinateOccurrences

/-! The paper's cross-bucket column family satisfies the exact coordinate
sort consumer. Runtime outer traversal and matrix padding remain separate. -/
namespace NearCubicWires.RepairOrdinary.CrossGrid
open SupplierPrinter SignedSortKey LeftPlaneCell CoordinateKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload {Rows Gates Columns : ℕ} (bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (id : Fin (Rows + Columns))
    (index : Fin (Gates * stableDominanceBucketCount Rows Columns bucketSize)) : Bool :=
  let p := finProdFinEquiv.symm index
  LeftCell.selected (p.2.val * (bucketSize + 1)) (bucketSize + 1)
    (stableDominanceRank leftScore rightScore p.1 (finSumFinEquiv.symm id)).val
    (coefficientBit negative (weight p.1) bit)

noncomputable def order {Rows Gates Columns : ℕ} (S K bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns)
    (index : Fin (Gates * stableDominanceBucketCount Rows Columns bucketSize)) : List (Fin (Rows + Columns)) :=
  (DominanceSort.sortedCopies S K leftScore rightScore (finProdFinEquiv.symm index).1).map stableDominanceCopyId

noncomputable def inputs {Rows Gates Columns : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) : List StablePartition.Record :=
  (List.finRange (Gates * stableDominanceBucketCount Rows Columns bucketSize)).flatMap (fun index =>
    let p := finProdFinEquiv.symm index
    generated K I index.val (p.2.val * (bucketSize + 1)) (bucketSize + 1)
      (coefficientBit negative (weight p.1) bit)
      (KeyLoop.indexed 0 (KeyLoop.dominanceEntries S K leftScore rightScore p.1)))

theorem inputs_columns {Rows Gates Columns : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ gate copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    inputs S K I bucketSize leftScore rightScore weight negative bit =
      columns I K (payload bucketSize leftScore rightScore weight negative bit)
        (order S K bucketSize leftScore rightScore) := by
  unfold inputs columns
  congr 1
  funext index
  exact generated_as_ids S K I index.val _ _ _ leftScore rightScore (finProdFinEquiv.symm index).1
    hsize (hlo _) (hhi _)

theorem inputs_perm_grid {Rows Gates Columns : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ gate copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    (inputs S K I bucketSize leftScore rightScore weight negative bit).Perm
      (grid I K (payload bucketSize leftScore rightScore weight negative bit)) := by
  rw [inputs_columns S K I bucketSize leftScore rightScore weight negative bit hsize hlo hhi]
  apply columns_perm_grid
  intro index
  exact dominance_ids_perm S K leftScore rightScore (finProdFinEquiv.symm index).1 hsize (hlo _) (hhi _)

theorem sorted_inputs {Rows Gates Columns : ℕ} (S K I bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (hsize : Rows + Columns ≤ 2 ^ K)
    (hinner : Gates * stableDominanceBucketCount Rows Columns bucketSize ≤ 2 ^ I)
    (hlo : ∀ gate copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ gate copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ))
    (req : SortCarrier.Request) (hreq : req.records = inputs S K I bucketSize leftScore rightScore weight negative bit) :
    SortCarrier.sorted req = grid I K (payload bucketSize leftScore rightScore weight negative bit) := by
  apply sorted_eq_grid I K _ req _ hinner hsize
  rw [hreq]
  exact inputs_perm_grid S K I bucketSize leftScore rightScore weight negative bit hsize hlo hhi

theorem left_entry {Rows Gates Columns : ℕ} (bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (weight : Fin Gates → ℤ)
    (negative : Bool) (bit : ℕ) (row : Fin Rows)
    (index : Fin (Gates * stableDominanceBucketCount Rows Columns bucketSize)) :
    payload bucketSize leftScore rightScore weight negative bit (stableDominanceCopyId (.inl row)) index =
      coefficientBit negative (reindexedLaterBucketLeft (stableBucketedDominanceLayout leftScore rightScore bucketSize)
        weight row index) bit := by
  unfold payload reindexedLaterBucketLeft
  rw [left_bit]
  simp [stableDominanceCopyId, LeftCell.selected, Nat.add_mul]

theorem left_id {Rows Columns : ℕ} (row : Fin Rows) :
    (stableDominanceCopyId (Columns := Columns) (.inl row)).val = row.val := rfl

end NearCubicWires.RepairOrdinary.CrossGrid

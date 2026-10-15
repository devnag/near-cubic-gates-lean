import Proof.MachineModel.OrdinaryCoordinateColumns

/-! The actual sequentially ranked output supplies the occurrence-column
payloads. This is a list-position proof, not a free executable projection. -/
namespace NearCubicWires.RepairOrdinary.CoordinateKey
open SignedSortKey RadixSemantics StablePartition SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem indexed_get (n : ℕ) (entries : List (ℤ × ℕ)) (i : ℕ) (hi : i < entries.length) :
    (KeyLoop.indexed n entries)[i]'(by simpa using hi) = (entries[i].1, entries[i].2, n + i) := by
  induction i generalizing n entries with
  | zero =>
    cases entries with
    | nil => simp at hi
    | cons e entries => rcases e with ⟨score, id⟩; simp [KeyLoop.indexed]
  | succ i ih =>
    cases entries with
    | nil => simp at hi
    | cons e entries =>
      rcases e with ⟨score, id⟩
      simpa [KeyLoop.indexed, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (n + 1) entries (by simpa using hi)

theorem generated_dominance {Rows Gates Columns : ℕ} (S K I inner a b : ℕ) (mask : Bool)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    generated K I inner a b mask (KeyLoop.indexed 0 (KeyLoop.dominanceEntries S K leftScore rightScore gate)) =
      (DominanceSort.sortedCopies S K leftScore rightScore gate).map
        (fun copy => key I K inner (stableDominanceCopyId copy).val
          (LeftCell.selected a b (stableDominanceRank leftScore rightScore gate copy).val mask)) := by
  unfold generated KeyLoop.dominanceEntries
  apply List.ext_getElem
  · simp
  · intro i hl hr
    have hi : i < (DominanceSort.sortedCopies S K leftScore rightScore gate).length := by simpa using hr
    have he : i < (KeyLoop.dominanceEntries S K leftScore rightScore gate).length := by
      simpa [KeyLoop.dominanceEntries] using hi
    have hrank := DominanceSort.sorted_rank S K leftScore rightScore gate hsize hlo hhi ⟨i, hi⟩
    change (stableDominanceRank leftScore rightScore gate
      ((DominanceSort.sortedCopies S K leftScore rightScore gate)[i]'hi)).val = i at hrank
    have hentry := indexed_get 0 (KeyLoop.dominanceEntries S K leftScore rightScore gate) i he
    unfold KeyLoop.dominanceEntries at hentry
    simp only [List.getElem_map]
    rw [hentry]
    simp only [Nat.zero_add, List.getElem_map]
    rw [hrank]

theorem generated_as_ids {Rows Gates Columns : ℕ} (S K I inner a b : ℕ) (mask : Bool)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    generated K I inner a b mask (KeyLoop.indexed 0 (KeyLoop.dominanceEntries S K leftScore rightScore gate)) =
      ((DominanceSort.sortedCopies S K leftScore rightScore gate).map stableDominanceCopyId).map
        (fun id => key I K inner id.val (LeftCell.selected a b
          (stableDominanceRank leftScore rightScore gate (finSumFinEquiv.symm id)).val mask)) := by
  rw [generated_dominance S K I inner a b mask leftScore rightScore gate hsize hlo hhi, List.map_map]
  apply List.map_congr_left
  intro copy _
  simp [stableDominanceCopyId]

end NearCubicWires.RepairOrdinary.CoordinateKey

import Proof.MachineModel.OrdinaryDominanceSort
import Mathlib.Order.WellFounded

/-! Output positions of the actual ordinary sorter are the existing paper
ranks. Consequently a sequential bucket counter supplies exactly the old
bucket labels; no alternative mathematical layout is introduced. -/
namespace NearCubicWires.RepairOrdinary.DominanceSort
open StablePartition RadixSemantics SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sorted_rank {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ))
    (i : Fin (sortedCopies scoreBits idBits leftScore rightScore gate).length) :
    (stableDominanceRank leftScore rightScore gate
      ((sortedCopies scoreBits idBits leftScore rightScore gate).get i)).val = i.val := by
  let output := sortedCopies scoreBits idBits leftScore rightScore gate
  obtain ⟨hp, hs⟩ := sorted_semantics scoreBits idBits leftScore rightScore gate hsize hlo hhi
  have hn : (copies Rows Columns).Nodup := List.nodup_ofFn_ofInjective finSumFinEquiv.symm.injective
  have hnodup : output.Nodup := hp.nodup_iff.mpr hn
  have hlength : output.length = Rows + Columns := by simpa [copies] using hp.length_eq
  let f : Fin output.length → Fin output.length := fun j =>
    (stableDominanceRank leftScore rightScore gate (output.get j)).cast hlength.symm
  have hm : StrictMono f := by
    intro a b hab
    have hle := hs.rel_get_of_lt hab
    have hne : stableDominanceKey leftScore rightScore gate (output.get a) ≠
        stableDominanceKey leftScore rightScore gate (output.get b) := by
      intro he
      have heq := stableDominanceKey_injective leftScore rightScore gate he
      exact (ne_of_lt hab) ((List.nodup_iff_injective_get.mp hnodup) heq)
    have hlt := (stableDominanceRank_lt_iff_key_lt leftScore rightScore gate
      (output.get a) (output.get b)).mpr (lt_of_le_of_ne hle hne)
    exact hlt
  have he : f i = i := le_antisymm (hm.le_id i) (hm.id_le i)
  exact congrArg Fin.val he

theorem sorted_bucket {Rows Gates Columns : ℕ} (scoreBits idBits bucketSize : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ))
    (i : Fin (sortedCopies scoreBits idBits leftScore rightScore gate).length) :
    (stableDominanceBucket (Rows := Rows) (Columns := Columns) (bucketSize := bucketSize)
      (stableDominanceRank leftScore rightScore gate
        ((sortedCopies scoreBits idBits leftScore rightScore gate).get i))).val =
      i.val / (bucketSize + 1) := by
  change (stableDominanceRank leftScore rightScore gate
      ((sortedCopies scoreBits idBits leftScore rightScore gate).get i)).val / (bucketSize + 1) = _
  rw [sorted_rank scoreBits idBits leftScore rightScore gate hsize hlo hhi]

end NearCubicWires.RepairOrdinary.DominanceSort

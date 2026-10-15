import Proof.MachineModel.OrdinaryCoordinateGrid

/-! Column-wise occurrence scans supply the complete-grid permutation needed
by the row-major sort consumer. Each column may use its own occurrence order. -/
namespace NearCubicWires.RepairOrdinary.CoordinateKey
open SignedSortKey RadixSemantics StablePartition SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flatMap_swap {α β γ : Type} (as : List α) (bs : List β) (f : α → β → γ) :
    (as.flatMap (fun a => bs.map (f a))).Perm (bs.flatMap (fun b => as.map (fun a => f a b))) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left (bs.map (f a))).trans (List.map_append_flatMap_perm bs (f a) (fun b => as.map (fun a => f a b)))

def columns {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool)
    (order : Fin Used → List (Fin Rows)) : List Record :=
  (List.finRange Used).flatMap (fun inner => (order inner).map
    (fun row => key I K inner.val row.val (payload row inner)))

theorem columns_perm_grid {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool)
    (order : Fin Used → List (Fin Rows)) (horder : ∀ inner, (order inner).Perm (List.finRange Rows)) :
    (columns I K payload order).Perm (grid I K payload) := by
  have hp := List.Perm.flatMap_left (List.finRange Used)
    (fun inner _ => (horder inner).map (fun row => key I K inner.val row.val (payload row inner)))
  have ht := flatMap_swap (List.finRange Used) (List.finRange Rows)
    (fun inner row => key I K inner.val row.val (payload row inner))
  have h := hp.trans ht
  rw [grid_rows]
  simpa only [columns, List.ofFn_eq_map, List.flatMap] using h

theorem columns_sorted {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool)
    (order : Fin Used → List (Fin Rows)) (horder : ∀ inner, (order inner).Perm (List.finRange Rows))
    (req : SortCarrier.Request) (hreq : req.records = columns I K payload order)
    (hi : Used ≤ 2 ^ I) (hk : Rows ≤ 2 ^ K) :
    SortCarrier.sorted req = grid I K payload := by
  apply sorted_eq_grid I K payload req _ hi hk
  rw [hreq]
  exact columns_perm_grid I K payload order horder

theorem dominance_ids_perm {Rows Gates Columns : ℕ} (S K : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    ((DominanceSort.sortedCopies S K leftScore rightScore gate).map stableDominanceCopyId).Perm
      (List.finRange (Rows + Columns)) := by
  have hp := ((DominanceSort.sorted_semantics S K leftScore rightScore gate hsize hlo hhi).1).map stableDominanceCopyId
  have he : (DominanceSort.copies Rows Columns).map stableDominanceCopyId = List.finRange (Rows + Columns) := by
    simp [DominanceSort.copies, stableDominanceCopyId, List.ofFn_eq_map]
  rw [he] at hp
  exact hp

end NearCubicWires.RepairOrdinary.CoordinateKey

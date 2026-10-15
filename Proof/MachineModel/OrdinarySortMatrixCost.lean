import Proof.MachineModel.OrdinarySortMatrix

/-! Dimension and bit-width costs at the actual sorted-grid matrix consumer. -/
namespace NearCubicWires.RepairOrdinary.SortMatrix
open LocalBitMultitape SupplierPrinter CoordinateKey GridRows LeftPlaneCell
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem keyed_row_length {Used : ℕ} (I K id : ℕ) (payload : Fin Used → Bool) :
    (recordsBits (List.ofFn (fun inner => key I K inner.val id (payload inner)))).length = Used * (2 * (I + K) + 3) := by
  have hs := SortCost.stream_length_of_width
    (List.ofFn (fun inner => key I K inner.val id (payload inner))) (I + K + 1) (by
      intro r hr
      obtain ⟨inner, rfl⟩ := List.mem_ofFn.mp hr
      exact key_width _ _ _ _ _)
  simp only [StablePartition.stream, List.length_append, List.length_singleton, List.length_ofFn] at hs
  have he : 2 * (I + K + 1) + 1 = 2 * (I + K) + 3 := by omega
  rw [he] at hs
  omega

theorem left_fields_length {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) :
    (MatrixRows.fields (leftRows I K payload)).length = Rows * (Used * (2 * (I + K) + 3)) := by
  simp [MatrixRows.fields, leftRows, List.flatMap, List.length_flatten, List.map_ofFn,
    Function.comp_def, keyed_row_length, List.ofFn_const]

theorem width_le {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) (req : SortCarrier.Request)
    (hgrid : SortCarrier.sorted req = grid I K payload) : SortPreparation.width req.records ≤ I + K + 1 := by
  have hw : ∀ r ∈ req.records, (RadixSemantics.word r).length = I + K + 1 := by
    intro r hr
    have hm := (SortCarrier.sorted_perm req).mem_iff.mpr hr
    rw [hgrid] at hm
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hm
    exact key_width _ _ _ _ _
  cases he : req.records with
  | nil => simp [SortPreparation.width, SortPreparation.firstWord]
  | cons r rs =>
    have h := hw r (by simp [he])
    simp only [SortPreparation.width, SortPreparation.firstWord, h, Nat.le_refl]

theorem joined_budget {Rows Columns Used Capacity : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) (req : SortCarrier.Request)
    (hgrid : SortCarrier.sorted req = grid I K payload) (hcap : Used ≤ Capacity) :
    2 * SortCarrier.budget req.records + 3 +
      ((MatrixRows.fields (leftRows I K payload)).length + Rows * (3 * Used + 2 * (Capacity - Used) + 11) + 1) ≤
      512 * ((Rows + Columns) * Used + Rows * Capacity + Rows + 1) * (I + K + 2) ^ 2 := by
  have hc : req.records.length = (Rows + Columns) * Used := by
    have h := (SortCarrier.sorted_perm req).length_eq
    rw [hgrid] at h
    simpa [grid] using h.symm
  have hw := width_le I K payload req hgrid
  have hs := SortCost.carrier_budget_le req
  have hm := Nat.mul_le_mul_left (128 * (req.records.length + 1))
    (Nat.pow_le_pow_left (by omega : SortPreparation.width req.records + 1 ≤ I + K + 2) 2)
  have hsort : SortCarrier.budget req.records ≤ 128 * ((Rows + Columns) * Used + 1) * (I + K + 2) ^ 2 := by
    rw [hc] at hm hs
    omega
  have hdim : Used + (Capacity - Used) = Capacity := Nat.add_sub_of_le hcap
  have hused : Rows * Used ≤ Rows * Capacity := Nat.mul_le_mul_left Rows hcap
  have hpad : Rows * (Capacity - Used) ≤ Rows * Capacity := Nat.mul_le_mul_left Rows (Nat.sub_le _ _)
  have hrow : (MatrixRows.fields (leftRows I K payload)).length + Rows * (3 * Used + 2 * (Capacity - Used) + 11) + 1 ≤
      16 * (Rows * Capacity + Rows + 1) * (I + K + 2) := by
    rw [left_fields_length]
    have hmrow := Nat.mul_le_mul_right (2 * (I + K) + 3) hused
    simp only [Nat.mul_add, Nat.mul_assoc] at hmrow ⊢
    nlinarith [Nat.zero_le (Rows * Capacity * (I + K)), Nat.zero_le (Rows * (I + K))]
  have hsq : I + K + 2 ≤ (I + K + 2) ^ 2 := by nlinarith
  have hrow' := hrow.trans (Nat.mul_le_mul_left (16 * (Rows * Capacity + Rows + 1)) hsq)
  have hone : 1 ≤ (I + K + 2) ^ 2 := by nlinarith
  nlinarith [Nat.zero_le (((Rows + Columns) * Used) * (I + K + 2) ^ 2),
    Nat.zero_le ((Rows * Capacity + Rows) * (I + K + 2) ^ 2)]

end NearCubicWires.RepairOrdinary.SortMatrix

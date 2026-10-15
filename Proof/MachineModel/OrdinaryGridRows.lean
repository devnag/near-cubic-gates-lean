import Proof.MachineModel.OrdinaryMatrixRows

/-! The actual sorted grid separates into its A-row prefix and B-row suffix.
Selecting the prefix and appending zeros gives the literal padded plane. -/
namespace NearCubicWires.RepairOrdinary.GridRows
open SupplierPrinter CoordinateKey LeftPlaneCell
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rows {Rows Used : ℕ} (I K : ℕ) (payload : Fin Rows → Fin Used → Bool) : List (List Record) :=
  List.ofFn (fun row => List.ofFn (fun inner => key I K inner.val row.val (payload row inner)))
def leftRows {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) : List (List Record) :=
  List.ofFn (fun row : Fin Rows => List.ofFn (fun inner : Fin Used =>
    key I K inner.val row.val (payload (row.castAdd Columns) inner)))
def rightRows {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) : List (List Record) :=
  List.ofFn (fun row : Fin Columns => List.ofFn (fun inner : Fin Used =>
    key I K inner.val (Rows + row.val) (payload (row.natAdd Rows) inner)))

theorem fields_flatten (rs : List (List Record)) : recordsBits rs.flatten = MatrixRows.fields rs := by
  induction rs with
  | nil => rfl
  | cons row rs ih => simpa [recordsBits, MatrixRows.fields] using congrArg (recordsBits row ++ ·) ih

theorem grid_split {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) :
    recordsBits (grid I K payload) = MatrixRows.fields (leftRows I K payload) ++ MatrixRows.fields (rightRows I K payload) := by
  rw [grid_rows, fields_flatten]
  have he : rows I K payload = leftRows I K payload ++ rightRows I K payload := by
    unfold rows
    rw [List.ofFn_add]
    rfl
  change MatrixRows.fields (rows I K payload) = _
  rw [he]
  simp [MatrixRows.fields]

@[simp] theorem left_length {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) : (leftRows I K payload).length = Rows := by simp [leftRows]

theorem left_width {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) : ∀ r ∈ leftRows I K payload, r.length = Used := by
  intro r hr
  obtain ⟨row, rfl⟩ := List.mem_ofFn.mp hr
  simp

theorem left_output {Rows Columns Used : ℕ} (I K pad : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) :
    MatrixRows.output pad (leftRows I K payload) =
      (List.ofFn (fun row : Fin Rows =>
        List.ofFn (fun inner : Fin Used => payload (row.castAdd Columns) inner) ++ List.replicate pad false)).flatten := by
  simp only [MatrixRows.output, leftRows, List.flatMap, List.map_ofFn, Function.comp_def]
  rfl

theorem signed_row {Rows Used Capacity : ℕ} (left : IntMatrix Rows Used) (negative : Bool)
    (bit : ℕ) (row : Fin Rows) (hcap : Used ≤ Capacity) :
    List.ofFn (fun inner : Fin Capacity => coefficientBit negative (padSignedInner left row inner) bit) =
      List.ofFn (fun inner : Fin Used => coefficientBit negative (left row inner) bit) ++ List.replicate (Capacity - Used) false := by
  obtain ⟨pad, rfl⟩ := Nat.exists_eq_add_of_le hcap
  rw [List.ofFn_add]
  have hl : (List.ofFn (fun inner : Fin Used =>
      coefficientBit negative (padSignedInner (Capacity := Used + pad) left row (inner.castLE (Nat.le_add_right Used pad))) bit)) =
      List.ofFn (fun inner : Fin Used => coefficientBit negative (left row inner) bit) := by
    apply congrArg List.ofFn
    funext inner
    simp [padSignedInner, inner.isLt]
  have hr : (List.ofFn (fun inner : Fin pad =>
      coefficientBit negative (padSignedInner (Capacity := Used + pad) left row (inner.natAdd Used)) bit)) =
      List.replicate pad false := by
    have he : (fun inner : Fin pad => coefficientBit negative
        (padSignedInner (Capacity := Used + pad) left row (inner.natAdd Used)) bit) = fun _ => false := by
      funext inner
      simp [padSignedInner]
    rw [he, List.ofFn_const]
  rw [hl, hr]
  simp

theorem signed_output {Rows Columns Used Capacity : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) (left : IntMatrix Rows Used)
    (negative : Bool) (bit : ℕ) (hcap : Used ≤ Capacity)
    (hleft : ∀ row inner, payload (row.castAdd Columns) inner = coefficientBit negative (left row inner) bit) :
    MatrixRows.output (Capacity - Used) (leftRows I K payload) =
      WilliamsLoaderForms.rowMajorBitMatrix (fun row inner =>
        coefficientBit negative (padSignedInner (Capacity := Capacity) left row inner) bit) := by
  rw [left_output]
  unfold WilliamsLoaderForms.rowMajorBitMatrix
  congr 1
  apply congrArg List.ofFn
  funext row
  rw [signed_row left negative bit row hcap]
  congr 1
  apply congrArg List.ofFn
  funext inner
  exact hleft row inner

end NearCubicWires.RepairOrdinary.GridRows

import Proof.MachineModel.OrdinaryMatrixRightPadding

/-! Literal inner-major grid consumed by the right-row selector. Its B-copy
suffix and trailing zero rows are the exact padded Boolean right matrix. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGrid
open SupplierPrinter CoordinateKey
open SourceInterfaces (BitMatrix)
open StablePartition (Record recordsBits)
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rows {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool) : List MatrixRightRows.Row :=
  List.ofFn (fun inner =>
    (List.ofFn (fun row : Fin U => key M M row.val inner.val (payload inner (row.castAdd U))),
     List.ofFn (fun column : Fin U => key M M (U+column.val) inner.val (payload inner (column.natAdd U)))))
def right {U Used : ℕ} (payload : Fin Used → Fin (U+U) → Bool) : BitMatrix Used U :=
  fun inner column => payload inner (column.natAdd U)

@[simp] theorem rows_length {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool) :
    (rows M payload).length=Used := by simp [rows]

theorem rows_width {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool) :
    ∀ row ∈ rows M payload,row.1.length=U ∧ row.2.length=U := by
  intro row hrow
  obtain ⟨inner,rfl⟩ := List.mem_ofFn.mp hrow
  simp

theorem rows_fields {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool) :
    recordsBits (grid M M payload)=MatrixRightRows.fields (rows M payload) := by
  rw [grid_rows,GridRows.fields_flatten]
  simp only [MatrixRows.fields,MatrixRightRows.fields,rows,List.flatMap,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext inner
  rw [List.ofFn_add]
  simp [recordsBits,List.flatMap_append,Nat.add_comm]
  rfl

theorem rows_output {U Used : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool) :
    MatrixRightRows.output (rows M payload)=rowMajorBitMatrix (right payload) := by
  simp only [MatrixRightRows.output,rows,List.flatMap,List.map_ofFn,Function.comp_def]
  rfl

theorem padded_word {U Used Capacity : ℕ} (matrix : BitMatrix Used U) (hcap : Used ≤ Capacity) :
    rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) matrix)=
      rowMajorBitMatrix matrix++List.replicate ((Capacity-Used)*U) false := by
  obtain ⟨pad,rfl⟩ := Nat.exists_eq_add_of_le hcap
  unfold rowMajorBitMatrix
  rw [List.ofFn_add,List.flatten_append]
  have hl : (List.ofFn (fun inner : Fin Used => List.ofFn (fun col : Fin U =>
      padBooleanInner (Capacity := Used+pad) matrix (inner.castLE (Nat.le_add_right Used pad)) col)))=
      List.ofFn (fun inner => List.ofFn (fun col => matrix inner col)) := by
    apply congrArg List.ofFn
    funext inner
    apply congrArg List.ofFn
    funext col
    simp [padBooleanInner,inner.isLt]
  have hr : (List.ofFn (fun inner : Fin pad => List.ofFn (fun col : Fin U =>
      padBooleanInner (Capacity := Used+pad) matrix (inner.natAdd Used) col)))=
      List.replicate pad (List.replicate U false) := by
    simp [padBooleanInner,List.ofFn_const]
  rw [hl,hr]
  simp

theorem literal_output {U Used Capacity : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (hcap : Used ≤ Capacity) :
    MatrixRightRows.output (rows M payload)++List.replicate ((Capacity-Used)*U) false=
      rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (right payload)) := by
  rw [rows_output,padded_word (right payload) hcap]

end NearCubicWires.RepairOrdinary.MatrixRightGrid

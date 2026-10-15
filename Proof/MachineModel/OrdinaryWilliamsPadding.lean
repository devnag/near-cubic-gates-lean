import Proof.MachineModel.OrdinaryMatrixPadRows
import Proof.MachineModel.OrdinaryWilliamsPaddedRequest

/-! Apply the actual streaming padding programs to the corrected source's
literal left/right matrices. Dimension-template generation is explicit. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPadding
open LocalBitMultitape SourceInterfaces ExecutableInterfaces RepairRepresentation
open WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padRows {u v c : ℕ} (a : BitMatrix u c) : BitMatrix v c :=
  fun row col => if h : row.val < u then a ⟨row.val, h⟩ col else false

def padColumns {u v c : ℕ} (a : BitMatrix c u) : BitMatrix c v :=
  fun row col => if h : col.val < u then a row ⟨col.val, h⟩ else false

theorem left_word {u v c : ℕ} (hu : u ≤ v) (a : BitMatrix u c) :
    rowMajorBitMatrix (padRows (v := v) a) = rowMajorBitMatrix a ++ List.replicate ((v - u) * c) false := by
  obtain ⟨pad, rfl⟩ := Nat.exists_eq_add_of_le hu
  unfold rowMajorBitMatrix
  rw [List.ofFn_add, List.flatten_append]
  have hleft : (List.ofFn (fun row : Fin u => List.ofFn (fun col : Fin c =>
      padRows (v := u + pad) a (row.castLE (Nat.le_add_right u pad)) col))).flatten =
      (List.ofFn (fun row : Fin u => List.ofFn (fun col : Fin c => a row col))).flatten := by
    congr 1
    apply congrArg List.ofFn
    funext row
    apply congrArg List.ofFn
    funext col
    simp [padRows, row.isLt]
  have hright : (List.ofFn (fun row : Fin pad => List.ofFn (fun col : Fin c =>
      padRows (v := u + pad) a (row.natAdd u) col))).flatten = List.replicate (pad * c) false := by
    simp [padRows, List.ofFn_const]
  simpa only [Nat.add_sub_cancel_left] using congrArg₂ (· ++ ·) hleft hright

theorem right_word {u v c : ℕ} (hu : u ≤ v) (a : BitMatrix c u) :
    rowMajorBitMatrix (padColumns (v := v) a) =
      MatrixPadRows.padded (v - u) (List.ofFn (fun row : Fin c => List.ofFn (fun col : Fin u => a row col))) := by
  obtain ⟨pad, rfl⟩ := Nat.exists_eq_add_of_le hu
  simp only [rowMajorBitMatrix, MatrixPadRows.padded, List.flatMap, List.map_ofFn, Function.comp_def,
    Nat.add_sub_cancel_left]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  rw [List.ofFn_add]
  have hleft : List.ofFn (fun col : Fin u => padColumns (v := u + pad) a row (col.castAdd pad)) =
      List.ofFn (fun col : Fin u => a row col) := by
    apply congrArg List.ofFn
    funext col
    simp [padColumns, col.isLt]
  have hright : List.ofFn (fun col : Fin pad => padColumns (v := u + pad) a row (col.natAdd u)) = List.replicate pad false := by
    simp [padColumns, List.ofFn_const]
  exact congrArg₂ (· ++ ·) hleft hright

theorem padded_left_word (r : RectangularProductRequest) :
    rowMajorBitMatrix (WilliamsPaddedRequest.left r) = rowMajorBitMatrix r.left ++
      List.replicate ((WilliamsPaddedRequest.dimension r.dimension - r.dimension) * rectangularInnerDimension r.dimension) false :=
  left_word (WilliamsPaddedRequest.dimension_ge r.dimension) r.left

theorem padded_right_word (r : RectangularProductRequest) :
    rowMajorBitMatrix (WilliamsPaddedRequest.right r) =
      MatrixPadRows.padded (WilliamsPaddedRequest.dimension r.dimension - r.dimension)
        (List.ofFn (fun row => List.ofFn (fun col => r.right row col))) :=
  right_word (WilliamsPaddedRequest.dimension_ge r.dimension) r.right

theorem left_run (r : RectangularProductRequest) (pre suffix : List Bool) :
    let v := WilliamsPaddedRequest.dimension r.dimension
    let c := rectangularInnerDimension r.dimension
    ∃ actual : ExecutionReceipt 4 10,
      runFrom MatrixPadRow.machine (2 * (v * c) + 9)
        (MatrixPadRow.config MatrixPadRow.machine.start (pre ++ rowMajorBitMatrix r.left ++ suffix) pre.length
          (natWord v) (r.dimension * c) ((v - r.dimension) * c)) = some actual ∧
      actual.final = MatrixPadRow.config 9 (pre ++ rowMajorBitMatrix r.left ++ suffix)
        (pre.length + r.dimension * c) (natWord v ++ rowMajorBitMatrix (WilliamsPaddedRequest.left r))
        (r.dimension * c) ((v - r.dimension) * c) ∧ actual.steps = 2 * (v * c) + 9 := by
  dsimp only
  let v := WilliamsPaddedRequest.dimension r.dimension
  let c := rectangularInnerDimension r.dimension
  obtain ⟨actual, hr, hf, hs⟩ := MatrixPadRow.row_run pre (rowMajorBitMatrix r.left) suffix (natWord v) ((v - r.dimension) * c)
  have hlen : (rowMajorBitMatrix r.left).length = r.dimension * c := WilliamsLoader.matrix_length r.left
  have hdim : r.dimension * c + (v - r.dimension) * c = v * c := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (WilliamsPaddedRequest.dimension_ge r.dimension)]
  rw [hlen, hdim] at hr hs
  rw [hlen] at hf
  have hout : natWord v ++ rowMajorBitMatrix r.left ++ List.replicate ((v - r.dimension) * c) false =
      natWord v ++ rowMajorBitMatrix (WilliamsPaddedRequest.left r) := by
    rw [padded_left_word]
    simp only [List.append_assoc, v, c]
  rw [hout] at hf
  exact ⟨actual, hr, hf, hs⟩

theorem right_run (r : RectangularProductRequest) (pre suffix out : List Bool) :
    let v := WilliamsPaddedRequest.dimension r.dimension
    let c := rectangularInnerDimension r.dimension
    ∃ actual : ExecutionReceipt 5 MatrixPadRows.stateCount,
      runFrom MatrixPadRows.machine (c * (2 * v + 12) + 3)
        (MatrixPadRows.config MatrixPadRows.machine.start (pre ++ rowMajorBitMatrix r.right ++ suffix) pre.length out
          r.dimension (v - r.dimension) c) = some actual ∧
      actual.final = MatrixPadRows.config (RepairSource.VerifierDecoding.RepeatMachine.phaseCode 10 3)
        (pre ++ rowMajorBitMatrix r.right ++ suffix) (pre.length + c * r.dimension)
        (out ++ rowMajorBitMatrix (WilliamsPaddedRequest.right r)) r.dimension (v - r.dimension) c ∧
      actual.steps ≤ c * (2 * v + 12) + 3 := by
  dsimp only
  let v := WilliamsPaddedRequest.dimension r.dimension
  let c := rectangularInnerDimension r.dimension
  let rows := List.ofFn (fun row => List.ofFn (fun col => r.right row col))
  have hw : ∀ row ∈ rows, row.length = r.dimension := by
    intro row hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    simp
  obtain ⟨actual, hr, hf, hs⟩ := MatrixPadRows.rows_run pre rows suffix out r.dimension (v - r.dimension) hw
  have hn : rows.length = c := by simp [rows, c]
  have hflat : rows.flatten = rowMajorBitMatrix r.right := rfl
  have hlen : rows.flatten.length = c * r.dimension := by rw [hflat]; exact WilliamsLoader.matrix_length r.right
  have hdim : r.dimension + (v - r.dimension) = v := Nat.add_sub_of_le (WilliamsPaddedRequest.dimension_ge r.dimension)
  rw [hn, hdim, hflat] at hr
  rw [hn, hlen, hflat, ← padded_right_word] at hf
  rw [hn, hdim] at hs
  exact ⟨actual, hr, hf, hs⟩

end NearCubicWires.RepairOrdinary.WilliamsPadding

import Proof.MachineModel.OrdinaryMatrixCropRows

/-! Instantiate the actual crop at the literal row-major, fixed-width
natural-cell encoding used by the corrected Williams source. -/
namespace NearCubicWires.RepairOrdinary.MatrixNaturalCrop
open LocalBitMultitape SourceInterfaces WilliamsLoaderForms
open WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word {R C : ℕ} (W : ℕ) (a : NatMatrix R C) : List Bool :=
  (List.ofFn (fun row => (List.ofFn (fun col => fixedWidthNatBits W (a row col))).flatten)).flatten

theorem encoded_word {R C : ℕ} (W : ℕ) (a : NatMatrix R C) :
    encodedNatCellTape W (rowMajorNatMatrix a) = word W a := by
  simp [encodedNatCellTape, rowMajorNatMatrix, word, List.flatten_flatten,
    List.flatMap, List.map_ofFn, Function.comp_def]

theorem take_bits (lo hi value : ℕ) :
    (fixedWidthNatBits (lo + hi) value).take lo = fixedWidthNatBits lo value := by
  apply List.ext_getElem
  · simp [fixedWidthNatBits]
  · intro i hleft hright
    simp [fixedWidthNatBits]

def rows {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) : List MatrixCropRows.Row :=
  List.ofFn (fun row : Fin R =>
    (List.ofFn (fun col : Fin C => fixedWidthNatBits W (a (row.castAdd P) (col.castAdd Q))),
      (List.ofFn (fun col : Fin Q => fixedWidthNatBits W (a (row.castAdd P) (col.natAdd C)))).flatten))

def suffix {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) : List Bool :=
  (List.ofFn (fun row : Fin P =>
    (List.ofFn (fun col : Fin (C + Q) => fixedWidthNatBits W (a (row.natAdd R) col))).flatten)).flatten

theorem source_split {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    MatrixCropRows.inputBits (rows W a) ++ suffix W a = word W a := by
  unfold word
  rw [List.ofFn_add, List.flatten_append]
  congr 1
  simp only [MatrixCropRows.inputBits, rows, List.flatMap, List.map_ofFn, Function.comp_def, MatrixCropRows.rowBits]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  rw [List.ofFn_add, List.flatten_append]
  rfl

theorem output_eq {R P C Q : ℕ} (lo hi : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    MatrixCropRows.outputBits lo (rows (lo + hi) a) =
      word lo (fun row : Fin R => fun col : Fin C => a (row.castAdd P) (col.castAdd Q)) := by
  simp only [MatrixCropRows.outputBits, rows, List.flatMap, List.map_ofFn, Function.comp_def,
    MatrixCropCells.kept, word]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  simp only [take_bits]

theorem row_count {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    (rows W a).length = R := by simp [rows]

theorem column_count {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    ∀ row ∈ rows W a, row.1.length = C := by
  intro row hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  simp

theorem tail_length {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    ∀ row ∈ rows W a, row.2.length = Q * W := by
  intro row hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  simp [fixedWidthNatBits, List.length_flatten, List.map_ofFn, Function.comp_def, List.ofFn_const]

theorem cell_length {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    ∀ row ∈ rows W a, ∀ cell ∈ row.1, cell.length = W := by
  intro row hm cell hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  simp [fixedWidthNatBits]

theorem consumed_length {R P C Q : ℕ} (W : ℕ) (a : NatMatrix (R + P) (C + Q)) :
    (MatrixCropRows.inputBits (rows W a)).length = R * ((C + Q) * W) := by
  simp [MatrixCropRows.inputBits, rows, MatrixCropRows.rowBits, List.length_flatMap, List.map_ofFn,
    Function.comp_def, List.length_flatten, fixedWidthNatBits, List.ofFn_const, Nat.add_mul]

theorem crop_run {R P C Q : ℕ} (lo hi : ℕ) (a : NatMatrix (R + P) (C + Q)) (out : List Bool) :
    ∃ r : ExecutionReceipt 7 MatrixCropRows.stateCount,
      runFrom MatrixCropRows.machine (R * (C * (2 * (lo + hi) + 12) + 2 * (Q * (lo + hi)) + 11) + 3)
        (MatrixCropRows.config MatrixCropRows.machine.start
          (encodedNatCellTape (lo + hi) (rowMajorNatMatrix a)) 0 out lo hi C (Q * (lo + hi)) R) = some r ∧
      r.final = MatrixCropRows.config (RepairSource.VerifierDecoding.RepeatMachine.phaseCode MatrixCropRow.stateCount 3)
        (encodedNatCellTape (lo + hi) (rowMajorNatMatrix a)) (R * ((C + Q) * (lo + hi)))
        (out ++ encodedNatCellTape lo (rowMajorNatMatrix
          (fun row : Fin R => fun col : Fin C => a (row.castAdd P) (col.castAdd Q)))) lo hi C (Q * (lo + hi)) R ∧
      r.steps ≤ R * (C * (2 * (lo + hi) + 12) + 2 * (Q * (lo + hi)) + 11) + 3 := by
  obtain ⟨r, hr, hf, hs⟩ := MatrixCropRows.rows_run [] (rows (lo + hi) a) (suffix (lo + hi) a) out
    lo hi C (Q * (lo + hi)) (column_count _ a) (tail_length _ a) (cell_length _ a)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, row_count, source_split, consumed_length,
    output_eq, ← encoded_word] at hr hf hs
  exact ⟨r, hr, hf, hs⟩

end NearCubicWires.RepairOrdinary.MatrixNaturalCrop

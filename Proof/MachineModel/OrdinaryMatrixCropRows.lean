import Proof.MachineModel.OrdinaryMatrixCropRow

/-! The whole physical rectangular crop. Two actual nested counted loops
retain row and column order, charge all skipped cells and bits, and preserve
the source plus all five reusable dimension templates. -/
namespace NearCubicWires.RepairOrdinary.MatrixCropRows
open LocalBitMultitape RepairSource.VerifierDecoding
open RepeatMachine (Control phaseCode)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Row := List (List Bool) × List Bool
def rowBits (row : Row) : List Bool := row.1.flatten ++ row.2
def inputBits (rows : List Row) : List Bool := rows.flatMap rowBits
def outputBits (lo : ℕ) (rows : List Row) : List Bool := rows.flatMap (fun row => MatrixCropCells.kept lo row.1)

def stateCount : ℕ := Fintype.card (Control MatrixCropRow.stateCount)
noncomputable def machine : Machine 7 stateCount := RepeatMachine.machine MatrixCropRow.machine (fun _ _ => true)

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (lo hi columns tail rows : ℕ) : Configuration 7 s :=
  TapeEmbedding.config ![1] ![CompareMachine.word rows]
    (MatrixCropRow.config state source pos out lo hi columns tail)

theorem repeat_config (phase : Fin 5) (q : Fin MatrixCropRow.stateCount) (source out : List Bool)
    (pos lo hi columns tail rows : ℕ) :
    RepeatMachine.cfg phase (MatrixCropRow.config q source pos out lo hi columns tail) rows 1 =
      config (phaseCode MatrixCropRow.stateCount phase) source pos out lo hi columns tail rows := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RepeatMachine.cfg, controlConfig, config, TapeEmbedding.config,
      MatrixCropRow.config, MatrixCropCells.config, MatrixCropCell.config, MatrixRawBlock.config, Fin.addCases]
  · funext i; fin_cases i <;> simp [RepeatMachine.cfg, controlConfig, config, TapeEmbedding.config,
      MatrixCropRow.config, MatrixCropCells.config, MatrixCropCell.config, MatrixRawBlock.config, Fin.addCases]

theorem split_at (rows : List Row) (i : ℕ) (hi : i < rows.length) :
    inputBits (rows.take i) ++ rowBits rows[i] ++ inputBits (rows.drop (i + 1)) = inputBits rows := by
  have h := congrArg (List.flatMap rowBits) (List.take_append_drop i rows)
  rw [List.flatMap_append, List.drop_eq_getElem_cons hi, List.flatMap_cons] at h
  simpa only [inputBits, List.append_assoc] using h

theorem rows_run (pre : List Bool) (rows : List Row) (suffix out : List Bool)
    (lo hi columns tail : ℕ)
    (hc : ∀ row ∈ rows, row.1.length = columns)
    (ht : ∀ row ∈ rows, row.2.length = tail)
    (hw : ∀ row ∈ rows, ∀ word ∈ row.1, word.length = lo + hi) :
    ∃ r : ExecutionReceipt 7 stateCount,
      runFrom machine (rows.length * (columns * (2 * (lo + hi) + 12) + 2 * tail + 11) + 3)
        (config machine.start (pre ++ inputBits rows ++ suffix) pre.length out lo hi columns tail rows.length) = some r ∧
      r.final = config (phaseCode MatrixCropRow.stateCount 3) (pre ++ inputBits rows ++ suffix)
        (pre.length + (inputBits rows).length) (out ++ outputBits lo rows) lo hi columns tail rows.length ∧
      r.steps ≤ rows.length * (columns * (2 * (lo + hi) + 12) + 2 * tail + 11) + 3 := by
  let source := pre ++ inputBits rows ++ suffix
  let boundary (i : ℕ) := MatrixCropRow.config MatrixCropRow.machine.start source
    (pre.length + (inputBits (rows.take i)).length) (out ++ outputBits lo (rows.take i)) lo hi columns tail
  have supplier (i : ℕ) (hi' : i < rows.length) :
      ∃ r, runFrom MatrixCropRow.machine (columns * (2 * (lo + hi) + 12) + 2 * tail + 8) (boundary i) = some r ∧
        r.steps ≤ columns * (2 * (lo + hi) + 12) + 2 * tail + 8 ∧
        r.final.heads = (boundary (i + 1)).heads ∧ r.final.tapes = (boundary (i + 1)).tapes := by
    let row := rows[i]
    have hm : row ∈ rows := List.getElem_mem hi'
    have hcolumns : row.1.length = columns := hc row hm
    have htail : row.2.length = tail := ht row hm
    have hsource : (pre ++ inputBits (rows.take i)) ++ row.1.flatten ++ row.2 ++
        (inputBits (rows.drop (i + 1)) ++ suffix) = source := by
      have hs := split_at rows i hi'
      change inputBits (rows.take i) ++ rowBits row ++ inputBits (rows.drop (i + 1)) = _ at hs
      calc
        _ = pre ++ (inputBits (rows.take i) ++ rowBits row ++ inputBits (rows.drop (i + 1))) ++ suffix := by
          simp only [rowBits, List.append_assoc]
        _ = source := by rw [hs]
    obtain ⟨r, hr, hf, hs⟩ := MatrixCropRow.row_run (pre ++ inputBits (rows.take i)) row.1 row.2
      (inputBits (rows.drop (i + 1)) ++ suffix) (out ++ outputBits lo (rows.take i)) lo hi (hw row hm)
    rw [hsource, hcolumns, htail, List.length_append] at hr hf
    rw [hcolumns, htail] at hs
    have hprefix : inputBits (rows.take (i + 1)) = inputBits (rows.take i) ++ rowBits row := by
      rw [List.take_succ_eq_append_getElem hi']
      simp only [inputBits, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, row]
    have houtput : outputBits lo (rows.take (i + 1)) = outputBits lo (rows.take i) ++ MatrixCropCells.kept lo row.1 := by
      rw [List.take_succ_eq_append_getElem hi']
      simp only [outputBits, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, row]
    have hh : r.final.heads = (boundary (i + 1)).heads := by
      rw [hf]
      simp only [boundary, hprefix, houtput, rowBits, List.length_append, htail, Nat.add_assoc, List.append_assoc]
      rfl
    have htp : r.final.tapes = (boundary (i + 1)).tapes := by
      rw [hf]
      simp only [boundary, houtput, List.append_assoc]
      rfl
    exact ⟨r, hr, hs, hh, htp⟩
  obtain ⟨r, hr, hs, hf⟩ := MatrixCountedRun.counted_run MatrixCropRow.machine rows.length
    (columns * (2 * (lo + hi) + 12) + 2 * tail + 8) boundary (fun _ _ => rfl) supplier
  have htime : columns * (2 * (lo + hi) + 12) + 2 * tail + 8 + 3 =
      columns * (2 * (lo + hi) + 12) + 2 * tail + 11 := by omega
  rw [htime] at hr hs
  have hfirst : boundary 0 = MatrixCropRow.config MatrixCropRow.machine.start source pre.length out lo hi columns tail := by
    simp only [boundary, List.take_zero, inputBits, outputBits, List.flatMap_nil, List.length_nil, Nat.add_zero, List.append_nil]
  have hlast : boundary rows.length = MatrixCropRow.config MatrixCropRow.machine.start source
      (pre.length + (inputBits rows).length) (out ++ outputBits lo rows) lo hi columns tail := by
    dsimp only [boundary]
    rw [List.take_length]
  rw [hfirst, repeat_config] at hr
  rw [hlast, repeat_config] at hf
  exact ⟨r, hr, hf, hs⟩

end NearCubicWires.RepairOrdinary.MatrixCropRows

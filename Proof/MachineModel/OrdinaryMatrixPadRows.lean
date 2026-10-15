import Proof.MachineModel.OrdinaryMatrixPadRow
import Proof.MachineModel.OrdinaryMatrixCountedRun

/-! Whole raw right-matrix zero padding with the shared actual counted
controller. The number of rows and both dimensions are physical templates. -/
namespace NearCubicWires.RepairOrdinary.MatrixPadRows
open LocalBitMultitape RepairSource.VerifierDecoding
open RepeatMachine (Control phaseCode)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stateCount : ℕ := Fintype.card (Control 10)
noncomputable def machine : Machine 5 stateCount := RepeatMachine.machine MatrixPadRow.machine (fun _ _ => true)

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (used pad count : ℕ) : Configuration 5 s :=
  TapeEmbedding.config ![1] ![CompareMachine.word count] (MatrixPadRow.config state source pos out used pad)

def padded (pad : ℕ) (rows : List (List Bool)) : List Bool := rows.flatMap (fun row => row ++ List.replicate pad false)

theorem repeat_config (phase : Fin 5) (q : Fin 10) (source out : List Bool) (pos used pad count : ℕ) :
    RepeatMachine.cfg phase (MatrixPadRow.config q source pos out used pad) count 1 =
      config (phaseCode 10 phase) source pos out used pad count := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RepeatMachine.cfg, controlConfig, config, TapeEmbedding.config,
      MatrixPadRow.config, MatrixRawBlock.config, Fin.addCases]
  · funext i; fin_cases i <;> simp [RepeatMachine.cfg, controlConfig, config, TapeEmbedding.config,
      MatrixPadRow.config, MatrixRawBlock.config, Fin.addCases]

theorem split_at (rows : List (List Bool)) (i : ℕ) (hi : i < rows.length) :
    (rows.take i).flatten ++ rows[i] ++ (rows.drop (i + 1)).flatten = rows.flatten := by
  have h := congrArg List.flatten (List.take_append_drop i rows)
  rw [List.flatten_append, List.drop_eq_getElem_cons hi, List.flatten_cons] at h
  simpa only [List.append_assoc] using h

theorem rows_run (pre : List Bool) (rows : List (List Bool)) (suffix out : List Bool)
    (used pad : ℕ) (hw : ∀ row ∈ rows, row.length = used) :
    ∃ r : ExecutionReceipt 5 stateCount,
      runFrom machine (rows.length * (2 * (used + pad) + 12) + 3)
        (config machine.start (pre ++ rows.flatten ++ suffix) pre.length out used pad rows.length) = some r ∧
      r.final = config (phaseCode 10 3) (pre ++ rows.flatten ++ suffix)
        (pre.length + rows.flatten.length) (out ++ padded pad rows) used pad rows.length ∧
      r.steps ≤ rows.length * (2 * (used + pad) + 12) + 3 := by
  let source := pre ++ rows.flatten ++ suffix
  let boundary (i : ℕ) := MatrixPadRow.config MatrixPadRow.machine.start source
    (pre.length + (rows.take i).flatten.length) (out ++ padded pad (rows.take i)) used pad
  have supplier (i : ℕ) (hi : i < rows.length) :
      ∃ r, runFrom MatrixPadRow.machine (2 * (used + pad) + 9) (boundary i) = some r ∧
        r.steps ≤ 2 * (used + pad) + 9 ∧
        r.final.heads = (boundary (i + 1)).heads ∧ r.final.tapes = (boundary (i + 1)).tapes := by
    let row := rows[i]
    have hrow : row.length = used := hw row (List.getElem_mem hi)
    have hsource : (pre ++ (rows.take i).flatten) ++ row ++ ((rows.drop (i + 1)).flatten ++ suffix) = source := by
      have hs := split_at rows i hi
      change (rows.take i).flatten ++ row ++ (rows.drop (i + 1)).flatten = _ at hs
      calc
        _ = pre ++ ((rows.take i).flatten ++ row ++ (rows.drop (i + 1)).flatten) ++ suffix := by
          simp only [List.append_assoc]
        _ = source := by rw [hs]
    obtain ⟨r, hr, hf, hs⟩ := MatrixPadRow.row_run (pre ++ (rows.take i).flatten) row
      ((rows.drop (i + 1)).flatten ++ suffix) (out ++ padded pad (rows.take i)) pad
    rw [hsource, hrow, List.length_append] at hr hf
    rw [hrow] at hs
    have hprefix : (rows.take (i + 1)).flatten = (rows.take i).flatten ++ row := by
      rw [List.take_succ_eq_append_getElem hi]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, row]
    have houtput : padded pad (rows.take (i + 1)) = padded pad (rows.take i) ++ row ++ List.replicate pad false := by
      rw [List.take_succ_eq_append_getElem hi]
      simp only [padded, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, row, List.append_assoc]
    have hh : r.final.heads = (boundary (i + 1)).heads := by
      rw [hf]
      simp only [boundary, hprefix, houtput, List.length_append, hrow, Nat.add_assoc, List.append_assoc]
      rfl
    have ht : r.final.tapes = (boundary (i + 1)).tapes := by
      rw [hf]
      simp only [boundary, houtput, List.append_assoc]
      rfl
    exact ⟨r, hr, hs.le, hh, ht⟩
  obtain ⟨r, hr, hs, hf⟩ := MatrixCountedRun.counted_run MatrixPadRow.machine rows.length
    (2 * (used + pad) + 9) boundary (fun _ _ => rfl) supplier
  have htime : 2 * (used + pad) + 9 + 3 = 2 * (used + pad) + 12 := by omega
  rw [htime] at hr hs
  have hfirst : boundary 0 = MatrixPadRow.config MatrixPadRow.machine.start source pre.length out used pad := by
    simp only [boundary, List.take_zero, List.flatten_nil, List.length_nil, Nat.add_zero, padded, List.flatMap_nil, List.append_nil]
  have hlast : boundary rows.length = MatrixPadRow.config MatrixPadRow.machine.start source
      (pre.length + rows.flatten.length) (out ++ padded pad rows) used pad := by
    dsimp only [boundary]
    rw [List.take_length]
  rw [hfirst, repeat_config] at hr
  rw [hlast, repeat_config] at hf
  exact ⟨r, hr, hf, hs⟩

end NearCubicWires.RepairOrdinary.MatrixPadRows

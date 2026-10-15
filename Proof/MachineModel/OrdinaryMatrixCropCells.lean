import Proof.MachineModel.OrdinaryMatrixCropCell
import Proof.MachineModel.OrdinaryMatrixCountedRun

/-! Whole row of fixed-width integer cells. The existing counted controller
executes the paid crop body and resets its column counter after exhaustion. -/
namespace NearCubicWires.RepairOrdinary.MatrixCropCells
open LocalBitMultitape
open RepairSource.VerifierDecoding
open RepairSource.VerifierDecoding.RepeatMachine (Control phaseCode)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stateCount : ℕ := Fintype.card (Control 10)
noncomputable def machine : Machine 5 stateCount := RepairSource.VerifierDecoding.RepeatMachine.machine MatrixCropCell.machine (fun _ _ => true)

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (lo hi count : ℕ) : Configuration 5 s :=
  TapeEmbedding.config ![1] ![CompareMachine.word count]
    (MatrixCropCell.config state source pos out lo hi)

def kept (lo : ℕ) (cells : List (List Bool)) : List Bool := cells.flatMap (List.take lo)

theorem repeat_config (phase : Fin 5) (q : Fin 10) (source out : List Bool)
    (pos lo hi count : ℕ) :
    RepeatMachine.cfg phase (MatrixCropCell.config q source pos out lo hi) count 1 =
      config (phaseCode 10 phase) source pos out lo hi count := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RepeatMachine.cfg, controlConfig, config, TapeEmbedding.config,
      MatrixCropCell.config, MatrixRawBlock.config, Fin.addCases]
  · funext i; fin_cases i <;> simp [RepeatMachine.cfg, controlConfig, config, TapeEmbedding.config,
      MatrixCropCell.config, MatrixRawBlock.config, Fin.addCases]

theorem split_at (cells : List (List Bool)) (i : ℕ) (hi : i < cells.length) :
    (cells.take i).flatten ++ cells[i] ++ (cells.drop (i + 1)).flatten = cells.flatten := by
  have h := congrArg List.flatten (List.take_append_drop i cells)
  rw [List.flatten_append, List.drop_eq_getElem_cons hi, List.flatten_cons] at h
  simpa only [List.append_assoc] using h

theorem cells_run (pre : List Bool) (cells : List (List Bool)) (suffix out : List Bool)
    (lo hi : ℕ) (hw : ∀ cell ∈ cells, cell.length = lo + hi) :
    ∃ r : ExecutionReceipt 5 stateCount,
      runFrom machine (cells.length * (2 * (lo + hi) + 12) + 3)
        (config machine.start (pre ++ cells.flatten ++ suffix) pre.length out lo hi cells.length) = some r ∧
      r.final = config (phaseCode 10 3) (pre ++ cells.flatten ++ suffix)
        (pre.length + cells.flatten.length) (out ++ kept lo cells) lo hi cells.length ∧
      r.steps ≤ cells.length * (2 * (lo + hi) + 12) + 3 := by
  let source := pre ++ cells.flatten ++ suffix
  let boundary (i : ℕ) := MatrixCropCell.config MatrixCropCell.machine.start source
    (pre.length + (cells.take i).flatten.length) (out ++ kept lo (cells.take i)) lo hi
  have supplier (i : ℕ) (hi' : i < cells.length) :
      ∃ r, runFrom MatrixCropCell.machine (2 * (lo + hi) + 9) (boundary i) = some r ∧
        r.steps ≤ 2 * (lo + hi) + 9 ∧
        r.final.heads = (boundary (i + 1)).heads ∧ r.final.tapes = (boundary (i + 1)).tapes := by
    let cell := cells[i]
    have hcell : cell.length = lo + hi := hw cell (List.getElem_mem hi')
    have hlo : (cell.take lo).length = lo := by simp [hcell]
    have hhi : (cell.drop lo).length = hi := by simp [hcell]
    have hsource : (pre ++ (cells.take i).flatten) ++ cell.take lo ++ cell.drop lo ++
        ((cells.drop (i + 1)).flatten ++ suffix) = source := by
      have hs := split_at cells i hi'
      change (cells.take i).flatten ++ cell ++ (cells.drop (i + 1)).flatten = _ at hs
      calc
        _ = pre ++ ((cells.take i).flatten ++ cell ++ (cells.drop (i + 1)).flatten) ++ suffix := by
          simp only [List.append_assoc, List.take_append_drop]
        _ = source := by rw [hs]
    obtain ⟨r, hr, hf, hsteps, _⟩ := MatrixCropCell.cell_run (pre ++ (cells.take i).flatten)
      (cell.take lo) (cell.drop lo) ((cells.drop (i + 1)).flatten ++ suffix) (out ++ kept lo (cells.take i))
    rw [hsource, hlo, hhi, List.length_append] at hr hf
    rw [hlo, hhi] at hsteps
    have hprefix : (cells.take (i + 1)).flatten = (cells.take i).flatten ++ cell := by
      rw [List.take_succ_eq_append_getElem hi']
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, cell]
    have hkept : kept lo (cells.take (i + 1)) = kept lo (cells.take i) ++ cell.take lo := by
      rw [List.take_succ_eq_append_getElem hi']
      simp only [kept, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, cell]
    have hh : r.final.heads = (boundary (i + 1)).heads := by
      rw [hf]
      simp only [boundary, hprefix, hkept, List.length_append, hcell, Nat.add_assoc, List.append_assoc]
      rfl
    have ht : r.final.tapes = (boundary (i + 1)).tapes := by
      rw [hf]
      simp only [boundary, hkept, List.append_assoc]
      rfl
    exact ⟨r, hr, hsteps.le, hh, ht⟩
  obtain ⟨r, hr, hs, hf⟩ := MatrixCountedRun.counted_run MatrixCropCell.machine cells.length
    (2 * (lo + hi) + 9) boundary (fun _ _ => rfl) supplier
  have htime : 2 * (lo + hi) + 9 + 3 = 2 * (lo + hi) + 12 := by omega
  rw [htime] at hr hs
  have hfirst : boundary 0 = MatrixCropCell.config MatrixCropCell.machine.start source pre.length out lo hi := by
    simp only [boundary, List.take_zero, List.flatten_nil, List.length_nil, Nat.add_zero, kept, List.flatMap_nil, List.append_nil]
  have hlast : boundary cells.length = MatrixCropCell.config MatrixCropCell.machine.start source
      (pre.length + cells.flatten.length) (out ++ kept lo cells) lo hi := by
    dsimp only [boundary]
    rw [List.take_length]
  rw [hfirst, repeat_config] at hr
  rw [hlast, repeat_config] at hf
  exact ⟨r, hr, hf, hs⟩

end NearCubicWires.RepairOrdinary.MatrixCropCells

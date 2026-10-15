import Proof.MachineModel.OrdinaryRecordCellLayout

/-! The actual annotated-record cell body. Rank extraction and the scalar
cell emitter share a physical rank tape; no intermediate rank stream is
materialized. Original occurrence records remain available for coordinates. -/
namespace NearCubicWires.RepairOrdinary.RecordCell
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_run (word : List Bool) (a b rank oldRank : ℕ) (pre suffix upperBacking recordBacking cloneBacking out : List Bool)
    (mask : Bool) (hfit : a + b < 2 ^ word.length) (hrank : rank < 2 ^ word.length)
    (hu : upperBacking.length ≤ 2 * word.length + 1) (hr : recordBacking.length ≤ 4 * word.length + 1)
    (hc : cloneBacking.length ≤ 4 * word.length + 1) :
    ∃ r : ExecutionReceipt 16 41,
      runFrom machine (68 * word.length + 51)
        (config machine.start word.length a b oldRank upperBacking recordBacking cloneBacking mask
          (pre ++ frame (word ++ binary word.length rank) ++ suffix) pre.length out) = some r ∧
      r.final = config 40 word.length a b rank (frame (binary word.length (a + b)))
        (frame (word ++ binary word.length rank)) (frame (word ++ binary word.length rank)) mask
        (pre ++ frame (word ++ binary word.length rank) ++ suffix) (pre.length + 4 * word.length + 1)
        (out ++ [LeftCell.selected a b rank mask]) ∧
      r.steps = 68 * word.length + 51 ∧
      r.peakTapeCells ≤ (pre ++ frame (word ++ binary word.length rank) ++ suffix).length +
        104 * word.length + out.length + 53 := by
  let width := word.length
  let source := pre ++ frame (word ++ binary width rank) ++ suffix
  let next := pre.length + 4 * width + 1
  let stored := frame (word ++ binary width rank)
  obtain ⟨loaded, hl, hlf, hls, hlp⟩ := RecordLoad.load_run word (binary width rank) pre suffix recordBacking
    cloneBacking (frame (binary width oldRank)) (by simp [width]) hr hc (by simp [width])
  let otherHeads : Fin 8 → ℕ := cellHeads out
  let otherTapes : Fin 8 → List Bool := cellTapes width a b upperBacking mask out
  have he := TapeEmbedding.run_embed RecordLoad.machine otherHeads otherTapes _ _ loaded hl
  have hload := TapeRenaming.run_rename layout (TapeEmbedding.machine 8 RecordLoad.machine) _ _ _ he
  let first := TapeRenaming.receipt layout (TapeEmbedding.receipt otherHeads otherTapes loaded)
  have hi : TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes
      (RecordLoad.config RecordLoad.machine.start
        (RecordLoad.workspace word (binary width rank) recordBacking cloneBacking (frame (binary width oldRank))) source pre.length)) =
      config load.start width a b oldRank upperBacking recordBacking cloneBacking mask source pre.length out := by
    exact place_initial RecordLoad.machine.start word rank oldRank a b upperBacking recordBacking cloneBacking mask source pre.length out
  have hload' : runFrom load (56 * width + 34)
      (config load.start width a b oldRank upperBacking recordBacking cloneBacking mask source pre.length out) = some first := by
    rw [← hi]
    exact hload
  obtain ⟨cell, hemit, hef, hes, hep⟩ := CellEmit.cell_run width a b rank upperBacking out mask hfit hrank hu
  have hee := TapeEmbedding.run_embed CellEmit.machine (recordHeads next) (recordTapes width stored stored source) _ _ cell hemit
  let second := TapeEmbedding.receipt (recordHeads next) (recordTapes width stored stored source) cell
  have firstFinal : first.final = config (20 : Fin 21) width a b rank upperBacking stored stored mask source next out := by
    change TapeRenaming.config layout (TapeEmbedding.config otherHeads otherTapes loaded.final) = _
    rw [hlf]
    exact place_loaded (20 : Fin 21) word rank a b upperBacking mask source next out
  have hmid : Composition.restart first.final emit.start =
      TapeEmbedding.config (recordHeads next) (recordTapes width stored stored source)
        (CellEmit.config CellEmit.machine.start (LocalCell.input width a b rank upperBacking mask) out) := by
    rw [firstFinal]
    rfl
  have hee' : runFrom emit (12 * width + 16) (Composition.restart first.final emit.start) = some second := by
    rw [hmid]
    exact hee
  have hj := Composition.run_join load emit (56 * width + 34) (12 * width + 16)
    (config load.start width a b oldRank upperBacking recordBacking cloneBacking mask source pre.length out) first second hload' hee'
  have htime : (56 * width + 34) + 1 + (12 * width + 16) = 68 * width + 51 := by omega
  refine ⟨Composition.joinedReceipt first second, by rw [htime] at hj; exact hj, ?_, ?_, ?_⟩
  · change Composition.rightConfig 21
      (TapeEmbedding.config (recordHeads next) (recordTapes width stored stored source) cell.final) = _
    rw [hef, emit_output]
    rfl
  · change loaded.steps + 1 + cell.steps = _
    dsimp only [width] at hes
    omega
  · change max (loaded.peakTapeCells + TapeEmbedding.extraCells otherTapes)
      (cell.peakTapeCells + TapeEmbedding.extraCells (recordTapes width stored stored source)) ≤ _
    simp [TapeEmbedding.extraCells, otherTapes, cellTapes, recordTapes, Fin.sum_univ_succ, stored, width]
    dsimp only [source]
    simp only [List.length_append, frame_length, binary_length] at hlp ⊢
    dsimp only [width] at hep
    omega

end NearCubicWires.RepairOrdinary.RecordCell

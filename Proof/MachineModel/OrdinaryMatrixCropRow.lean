import Proof.MachineModel.OrdinaryMatrixCropCells

/-! The complete crop of one Williams output row: retain the requested
columns and low bits, then skip the source row's remaining columns. -/
namespace NearCubicWires.RepairOrdinary.MatrixCropRow
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (lo hi count tail : ℕ) : Configuration 6 s :=
  TapeEmbedding.config ![1] ![UnaryTemplate.tape tail]
    (MatrixCropCells.config state source pos out lo hi count)

def layout : Fin 6 ≃ Fin 6 where
  toFun := ![5, 1, 2, 0, 3, 4]
  invFun := ![3, 1, 2, 4, 5, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

noncomputable def cells : Machine 6 MatrixCropCells.stateCount := TapeEmbedding.machine 1 MatrixCropCells.machine
def skip : Machine 6 5 := TapeRenaming.machine layout (TapeEmbedding.machine 3 (MatrixRawBlock.machine false))
def stateCount : ℕ := MatrixCropCells.stateCount + 5
noncomputable def machine : Machine 6 stateCount := Composition.machine cells skip

theorem place (state : Fin 5) (lo hi count tail : ℕ) (source out : List Bool) (pos : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config ![1, 1, 1]
      ![UnaryTemplate.tape lo, UnaryTemplate.tape hi, CompareMachine.word count]
      (MatrixRawBlock.config state (UnaryTemplate.tape tail) 1 source pos out)) =
      config state source pos out lo hi count tail := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, MatrixRawBlock.config,
      config, MatrixCropCells.config, MatrixCropCell.config, layout, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, MatrixRawBlock.config,
      config, MatrixCropCells.config, MatrixCropCell.config, layout, Fin.addCases]

theorem row_run (pre : List Bool) (words : List (List Bool)) (tail suffix out : List Bool)
    (lo hi : ℕ) (hw : ∀ word ∈ words, word.length = lo + hi) :
    ∃ r : ExecutionReceipt 6 stateCount,
      runFrom machine (words.length * (2 * (lo + hi) + 12) + 2 * tail.length + 8)
        (config machine.start (pre ++ words.flatten ++ tail ++ suffix) pre.length out lo hi words.length tail.length) = some r ∧
      r.final = config ((4 : Fin 5).natAdd MatrixCropCells.stateCount)
        (pre ++ words.flatten ++ tail ++ suffix) (pre.length + words.flatten.length + tail.length)
        (out ++ MatrixCropCells.kept lo words) lo hi words.length tail.length ∧
      r.steps ≤ words.length * (2 * (lo + hi) + 12) + 2 * tail.length + 8 := by
  let source := pre ++ words.flatten ++ tail ++ suffix
  let appended := out ++ MatrixCropCells.kept lo words
  obtain ⟨first, hr, hf, hs⟩ := MatrixCropCells.cells_run pre words (tail ++ suffix) out lo hi hw
  have hsource : pre ++ words.flatten ++ (tail ++ suffix) = source := by simp [source, List.append_assoc]
  rw [hsource] at hr hf
  have he := TapeEmbedding.run_embed MatrixCropCells.machine ![1] ![UnaryTemplate.tape tail.length] _ _ first hr
  obtain ⟨second, hrun, hfinal, hsteps, _⟩ := MatrixRawBlock.block_run false (pre ++ words.flatten) tail suffix appended
  let extraHeads : Fin 3 → ℕ := ![1, 1, 1]
  let extraTapes := ![UnaryTemplate.tape lo, UnaryTemplate.tape hi, CompareMachine.word words.length]
  have he2 := TapeEmbedding.run_embed (MatrixRawBlock.machine false) extraHeads extraTapes _ _ second hrun
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 3 (MatrixRawBlock.machine false)) _ _ _ he2
  have hmid : Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape tail.length] first.final) skip.start =
      config 0 source (pre ++ words.flatten).length appended lo hi words.length tail.length := by
    rw [hf]
    simp only [List.length_append]
    rfl
  have hn' : runFrom skip (2 * tail.length + 4)
      (Composition.restart (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape tail.length] first).final skip.start) =
      some (TapeRenaming.receipt layout (TapeEmbedding.receipt extraHeads extraTapes second)) := by
    change runFrom skip _ (Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape tail.length] first.final) skip.start) = _
    rw [hmid]
    simpa only [extraHeads, extraTapes, place, skip] using hn
  have hj := Composition.run_join cells skip (words.length * (2 * (lo + hi) + 12) + 3) (2 * tail.length + 4) _
    (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape tail.length] first)
    (TapeRenaming.receipt layout (TapeEmbedding.receipt extraHeads extraTapes second)) he hn'
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape tail.length] first)
    (TapeRenaming.receipt layout (TapeEmbedding.receipt extraHeads extraTapes second)), ?_, ?_, ?_⟩
  · have htime : words.length * (2 * (lo + hi) + 12) + 3 + 1 + (2 * tail.length + 4) =
        words.length * (2 * (lo + hi) + 12) + 2 * tail.length + 8 := by omega
    rw [htime] at hj
    exact hj
  · change Composition.rightConfig MatrixCropCells.stateCount (TapeRenaming.config layout
      (TapeEmbedding.config extraHeads extraTapes second.final)) = _
    rw [hfinal]
    change Composition.rightConfig MatrixCropCells.stateCount (TapeRenaming.config layout
      (TapeEmbedding.config ![1, 1, 1] ![UnaryTemplate.tape lo, UnaryTemplate.tape hi, CompareMachine.word words.length]
        (MatrixRawBlock.config 4 (UnaryTemplate.tape tail.length) 1 source
          ((pre ++ words.flatten).length + tail.length) (appended ++ MatrixRawBlock.selected false tail)))) = _
    rw [place]
    simp only [MatrixRawBlock.selected, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_append]
    rfl
  · change first.steps + 1 + second.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.MatrixCropRow

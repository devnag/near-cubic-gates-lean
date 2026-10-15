import Proof.MachineModel.OrdinaryMatrixRawBlock

/-! A physical Williams cell crop: copy the low output-width bits, skip
the remaining source-width bits, and restore both dimension templates. -/
namespace NearCubicWires.RepairOrdinary.MatrixCropCell
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (lo hi : ℕ) : Configuration 4 s :=
  TapeEmbedding.config ![1] ![UnaryTemplate.tape hi]
    (MatrixRawBlock.config state (UnaryTemplate.tape lo) 1 source pos out)

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ)
    (out : List Bool) (lo hi : ℕ) :
    (config state source pos out lo hi).tapeCells = source.length + out.length + lo + hi + 4 := by
  simp [config, TapeEmbedding.config_cells, TapeEmbedding.extraCells]
  omega

def layout : Fin 4 ≃ Fin 4 where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def low : Machine 4 5 := TapeEmbedding.machine 1 (MatrixRawBlock.machine true)
def high : Machine 4 5 := TapeRenaming.machine layout (TapeEmbedding.machine 1 (MatrixRawBlock.machine false))
def machine : Machine 4 10 := Composition.machine low high

theorem place (state : Fin 5) (lo hi : ℕ) (source out : List Bool) (pos : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config ![1] ![UnaryTemplate.tape lo]
      (MatrixRawBlock.config state (UnaryTemplate.tape hi) 1 source pos out)) =
      config state source pos out lo hi := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, MatrixRawBlock.config,
      config, layout, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, MatrixRawBlock.config,
      config, layout, Fin.addCases]

theorem cell_run (pre lowBits highBits suffix out : List Bool) :
    ∃ r : ExecutionReceipt 4 10,
      runFrom machine (2 * (lowBits.length + highBits.length) + 9)
        (config machine.start (pre ++ lowBits ++ highBits ++ suffix) pre.length out lowBits.length highBits.length) = some r ∧
      r.final = config 9 (pre ++ lowBits ++ highBits ++ suffix)
        (pre.length + lowBits.length + highBits.length) (out ++ lowBits) lowBits.length highBits.length ∧
      r.steps = 2 * (lowBits.length + highBits.length) + 9 ∧
      r.peakTapeCells ≤ (pre ++ lowBits ++ highBits ++ suffix).length + out.length + 2 * (lowBits.length + highBits.length) + 4 := by
  let source := pre ++ lowBits ++ highBits ++ suffix
  let appended := out ++ lowBits
  obtain ⟨first, hr, hf, hs, hp⟩ := MatrixRawBlock.block_run true pre lowBits (highBits ++ suffix) out
  have hsource : pre ++ lowBits ++ (highBits ++ suffix) = source := by simp [source, List.append_assoc]
  rw [hsource] at hr hf hp
  have he := TapeEmbedding.run_embed (MatrixRawBlock.machine true) ![1] ![UnaryTemplate.tape highBits.length] _ _ first hr
  obtain ⟨second, hrun, hfinal, hsteps, hpeak⟩ := MatrixRawBlock.block_run false (pre ++ lowBits) highBits suffix appended
  have he2 := TapeEmbedding.run_embed (MatrixRawBlock.machine false) ![1] ![UnaryTemplate.tape lowBits.length] _ _ second hrun
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 1 (MatrixRawBlock.machine false)) _ _ _ he2
  have hmid : Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape highBits.length] first.final) high.start =
      config 0 source (pre ++ lowBits).length appended lowBits.length highBits.length := by
    rw [hf]
    simp only [List.length_append]
    rfl
  have hn' : runFrom high (2 * highBits.length + 4)
      (Composition.restart (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape highBits.length] first).final high.start) =
      some (TapeRenaming.receipt layout (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape lowBits.length] second)) := by
    change runFrom high _ (Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape highBits.length] first.final) high.start) = _
    rw [hmid]
    simpa only [place, high] using hn
  have hj := Composition.run_join low high (2 * lowBits.length + 4) (2 * highBits.length + 4) _
    (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape highBits.length] first)
    (TapeRenaming.receipt layout (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape lowBits.length] second)) he hn'
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape highBits.length] first)
    (TapeRenaming.receipt layout (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape lowBits.length] second)), ?_, ?_, ?_, ?_⟩
  · have htime : 2 * lowBits.length + 4 + 1 + (2 * highBits.length + 4) = 2 * (lowBits.length + highBits.length) + 9 := by omega
    rw [htime] at hj
    exact hj
  · change Composition.rightConfig 5 (TapeRenaming.config layout
      (TapeEmbedding.config ![1] ![UnaryTemplate.tape lowBits.length] second.final)) = _
    rw [hfinal, place]
    simp only [MatrixRawBlock.selected, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_append]
    rfl
  · change first.steps + 1 + second.steps = _
    omega
  · change max (first.peakTapeCells + TapeEmbedding.extraCells ![UnaryTemplate.tape highBits.length])
      (second.peakTapeCells + TapeEmbedding.extraCells ![UnaryTemplate.tape lowBits.length]) ≤ _
    simp only [TapeEmbedding.extraCells, Fin.sum_univ_one, Matrix.cons_val_zero, UnaryTemplate.tape_length]
    simp only [source, appended, List.length_append] at hp hpeak ⊢
    omega

end NearCubicWires.RepairOrdinary.MatrixCropCell

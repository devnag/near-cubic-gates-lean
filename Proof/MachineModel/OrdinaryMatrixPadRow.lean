import Proof.MachineModel.OrdinaryMatrixRawBlock
import Proof.MachineModel.OrdinaryZeroBlock

/-! Raw matrix row padding: sequentially copy the actual source row and
append the physical template's number of zeros. Both templates are reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixPadRow
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (used pad : ℕ) : Configuration 4 s :=
  TapeEmbedding.config ![1] ![UnaryTemplate.tape pad]
    (MatrixRawBlock.config state (UnaryTemplate.tape used) 1 source pos out)

def layout : Fin 4 ≃ Fin 4 where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def row : Machine 4 5 := TapeEmbedding.machine 1 (MatrixRawBlock.machine true)
def zeros : Machine 4 5 := TapeRenaming.machine layout (TapeEmbedding.machine 2 ZeroBlock.machine)
def machine : Machine 4 10 := Composition.machine row zeros

theorem place (state : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) (used pad : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config ![1, pos] ![UnaryTemplate.tape used, source]
      (ZeroBlock.config state (UnaryTemplate.tape pad) 1 out)) = config state source pos out used pad := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, ZeroBlock.config,
      config, MatrixRawBlock.config, layout, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, ZeroBlock.config,
      config, MatrixRawBlock.config, layout, Fin.addCases]

theorem row_run (pre bits suffix out : List Bool) (pad : ℕ) :
    ∃ r : ExecutionReceipt 4 10,
      runFrom machine (2 * (bits.length + pad) + 9)
        (config machine.start (pre ++ bits ++ suffix) pre.length out bits.length pad) = some r ∧
      r.final = config 9 (pre ++ bits ++ suffix) (pre.length + bits.length)
        (out ++ bits ++ List.replicate pad false) bits.length pad ∧
      r.steps = 2 * (bits.length + pad) + 9 := by
  let source := pre ++ bits ++ suffix
  let appended := out ++ bits
  let next := pre.length + bits.length
  obtain ⟨first, hr, hf, hs, _⟩ := MatrixRawBlock.block_run true pre bits suffix out
  have he := TapeEmbedding.run_embed (MatrixRawBlock.machine true) ![1] ![UnaryTemplate.tape pad] _ _ first hr
  obtain ⟨second, hrun, hfinal, hsteps, _⟩ := ZeroBlock.block_run pad appended
  have he2 := TapeEmbedding.run_embed ZeroBlock.machine ![1, next] ![UnaryTemplate.tape bits.length, source] _ _ second hrun
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 ZeroBlock.machine) _ _ _ he2
  have hmid : Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape pad] first.final) zeros.start =
      config 0 source next appended bits.length pad := by rw [hf]; rfl
  have hn' : runFrom zeros (2 * pad + 4)
      (Composition.restart (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape pad] first).final zeros.start) =
      some (TapeRenaming.receipt layout (TapeEmbedding.receipt ![1, next] ![UnaryTemplate.tape bits.length, source] second)) := by
    change runFrom zeros _ (Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape pad] first.final) zeros.start) = _
    rw [hmid]
    simpa only [place, zeros] using hn
  have hj := Composition.run_join row zeros (2 * bits.length + 4) (2 * pad + 4) _
    (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape pad] first)
    (TapeRenaming.receipt layout (TapeEmbedding.receipt ![1, next] ![UnaryTemplate.tape bits.length, source] second)) he hn'
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape pad] first)
    (TapeRenaming.receipt layout (TapeEmbedding.receipt ![1, next] ![UnaryTemplate.tape bits.length, source] second)), ?_, ?_, ?_⟩
  · have htime : 2 * bits.length + 4 + 1 + (2 * pad + 4) = 2 * (bits.length + pad) + 9 := by omega
    rw [htime] at hj
    exact hj
  · change Composition.rightConfig 5 (TapeRenaming.config layout
      (TapeEmbedding.config ![1, next] ![UnaryTemplate.tape bits.length, source] second.final)) = _
    rw [hfinal, place]
    rfl
  · change first.steps + 1 + second.steps = _
    omega

end NearCubicWires.RepairOrdinary.MatrixPadRow

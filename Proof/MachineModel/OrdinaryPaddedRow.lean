import Proof.MachineModel.OrdinaryZeroBlock

/-! Actual selected matrix row: consume its keyed payloads, append a zero
suffix, and restore both reusable dimension templates. -/
namespace NearCubicWires.RepairOrdinary.PaddedRow
open LocalBitMultitape
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool)
    (used pad : ℕ) : Configuration 4 s :=
  TapeEmbedding.config ![1] ![UnaryTemplate.tape pad]
    (PayloadCounted.config state source pos out 1 (UnaryTemplate.tape used))
@[simp] theorem config_cells {s : ℕ} (state : Fin s) (source : List Bool) (pos : ℕ)
    (out : List Bool) (used pad : ℕ) :
    (config state source pos out used pad).tapeCells = source.length + out.length + used + pad + 4 := by
  simp [config, TapeEmbedding.config_cells, TapeEmbedding.extraCells]
  omega

def layout : Fin 4 ≃ Fin 4 where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 4 → Fin 4) = ![2, 1, 3, 0] := rfl
def row : Machine 4 17 := TapeEmbedding.machine 1 (PayloadRow.machine true)
def zeros : Machine 4 5 := TapeRenaming.machine layout (TapeEmbedding.machine 2 ZeroBlock.machine)
def machine : Machine 4 22 := Composition.machine row zeros

theorem place (state : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) (used pad : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config ![pos, 1] ![source, UnaryTemplate.tape used]
      (ZeroBlock.config state (UnaryTemplate.tape pad) 1 out)) = config state source pos out used pad := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, ZeroBlock.config,
      config, PayloadCounted.config, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, ZeroBlock.config,
      config, PayloadCounted.config, Fin.addCases]

theorem zeros_run (source : List Bool) (pos : ℕ) (out : List Bool) (used pad : ℕ) :
    ∃ r : ExecutionReceipt 4 5,
      runFrom zeros (2 * pad + 4) (config 0 source pos out used pad) = some r ∧
      r.final = config 4 source pos (out ++ List.replicate pad false) used pad ∧
      r.steps = 2 * pad + 4 ∧
      r.peakTapeCells ≤ source.length + out.length + used + 2 * pad + 4 := by
  obtain ⟨r, hr, hf, hs, hp⟩ := ZeroBlock.block_run pad out
  have he := TapeEmbedding.run_embed ZeroBlock.machine ![pos, 1] ![source, UnaryTemplate.tape used] _ _ r hr
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 ZeroBlock.machine) _ _ _ he
  refine ⟨TapeRenaming.receipt layout (TapeEmbedding.receipt ![pos, 1] ![source, UnaryTemplate.tape used] r), ?_, ?_, hs, ?_⟩
  · simpa only [place, zeros] using hn
  · change TapeRenaming.config layout (TapeEmbedding.config ![pos, 1] ![source, UnaryTemplate.tape used] r.final) = _
    rw [hf, place]
  · change r.peakTapeCells + TapeEmbedding.extraCells ![source, UnaryTemplate.tape used] ≤ _
    simp [TapeEmbedding.extraCells, Fin.sum_univ_succ]
    omega

theorem row_run (pre : List Bool) (records : List Record) (suffix out : List Bool) (pad : ℕ) :
    ∃ r : ExecutionReceipt 4 22,
      runFrom machine ((recordsBits records).length + 3 * records.length + 2 * pad + 9)
        (config machine.start (pre ++ recordsBits records ++ suffix) pre.length out records.length pad) = some r ∧
      r.final = config 21 (pre ++ recordsBits records ++ suffix)
        (pre.length + (recordsBits records).length) (out ++ records.map Prod.fst ++ List.replicate pad false)
        records.length pad ∧
      r.steps = (recordsBits records).length + 3 * records.length + 2 * pad + 9 ∧
      r.peakTapeCells ≤ (pre ++ recordsBits records ++ suffix).length + out.length + 2 * records.length + 2 * pad + 4 := by
  let source := pre ++ recordsBits records ++ suffix
  let next := pre.length + (recordsBits records).length
  let appended := out ++ records.map Prod.fst
  obtain ⟨first, hr, hf, hs, hp⟩ := PayloadRow.row_run true pre records suffix out
  have he := TapeEmbedding.run_embed (PayloadRow.machine true) ![1] ![UnaryTemplate.tape pad] _ _ first hr
  obtain ⟨second, hrun, hfinal, hsteps, hpeak⟩ := zeros_run source next appended records.length pad
  have hmid : Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape pad] first.final) zeros.start =
      config 0 source next appended records.length pad := by
    rw [hf]
    rfl
  have hrun' : runFrom zeros (2 * pad + 4)
      (Composition.restart (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape pad] first).final zeros.start) = some second := by
    change runFrom zeros (2 * pad + 4)
      (Composition.restart (TapeEmbedding.config ![1] ![UnaryTemplate.tape pad] first.final) zeros.start) = some second
    rw [hmid]
    exact hrun
  have hj := Composition.run_join row zeros ((recordsBits records).length + 3 * records.length + 4)
    (2 * pad + 4) _ (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape pad] first) second he hrun'
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt ![1] ![UnaryTemplate.tape pad] first) second, ?_, ?_, ?_, ?_⟩
  · have htime : (recordsBits records).length + 3 * records.length + 4 + 1 + (2 * pad + 4) =
        (recordsBits records).length + 3 * records.length + 2 * pad + 9 := by omega
    rw [htime] at hj
    exact hj
  · change Composition.rightConfig 17 second.final = _
    rw [hfinal]
    rfl
  · change first.steps + 1 + second.steps = _
    omega
  · change max (first.peakTapeCells + TapeEmbedding.extraCells ![UnaryTemplate.tape pad]) second.peakTapeCells ≤ _
    simp [TapeEmbedding.extraCells]
    dsimp only [source, next, appended] at hpeak
    simp only [List.length_append, List.length_map] at hpeak hp ⊢
    omega

end NearCubicWires.RepairOrdinary.PaddedRow

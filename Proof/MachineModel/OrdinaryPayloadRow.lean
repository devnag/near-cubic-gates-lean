import Proof.MachineModel.OrdinaryPayloadCounted

/-! Counted row traversal followed by an actual reset of its dimension
template. Source and growing matrix-output cursors remain at their endpoints. -/
namespace NearCubicWires.RepairOrdinary.PayloadRow
open LocalBitMultitape
open StablePartition (Record recordsBits)
open PayloadCounted (config selected)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 3 ≃ Fin 3 where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 3 → Fin 3) = ![1, 2, 0] := rfl
def reset : Machine 3 3 := TapeRenaming.machine layout (TapeEmbedding.machine 2 UnaryTemplate.machine)
def machine (keep : Bool) : Machine 3 17 := Composition.machine (PayloadCounted.machine keep) reset

theorem place (state : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) (count head : ℕ) :
    TapeRenaming.config layout (TapeEmbedding.config ![pos, out.length] ![source, out]
      (UnaryTemplate.config state (UnaryTemplate.tape count) head)) = config state source pos out head (UnaryTemplate.tape count) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, UnaryTemplate.config, config, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, UnaryTemplate.config, config, Fin.addCases]

theorem reset_run (source : List Bool) (pos : ℕ) (out : List Bool) (count : ℕ) :
    ∃ r : ExecutionReceipt 3 3,
      runFrom reset (count + 2) (config 0 source pos out (count + 1) (UnaryTemplate.tape count)) = some r ∧
      r.final = config 2 source pos out 1 (UnaryTemplate.tape count) ∧ r.steps = count + 2 ∧
      r.peakTapeCells ≤ source.length + out.length + count + 2 := by
  obtain ⟨r, hr, hf, hs, hp⟩ := UnaryTemplate.reset_run count
  have he := TapeEmbedding.run_embed UnaryTemplate.machine ![pos, out.length] ![source, out] _ _ r hr
  have hn := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 UnaryTemplate.machine) _ _ _ he
  refine ⟨TapeRenaming.receipt layout (TapeEmbedding.receipt ![pos, out.length] ![source, out] r), ?_, ?_, hs, ?_⟩
  · simpa only [place, reset] using hn
  · change TapeRenaming.config layout (TapeEmbedding.config ![pos, out.length] ![source, out] r.final) = _
    rw [hf, place]
  · change r.peakTapeCells + TapeEmbedding.extraCells ![source, out] ≤ _
    simp [TapeEmbedding.extraCells, Fin.sum_univ_succ]
    omega

theorem row_run (keep : Bool) (pre : List Bool) (records : List Record) (suffix out : List Bool) :
    ∃ r : ExecutionReceipt 3 17,
      runFrom (machine keep) ((recordsBits records).length + 3 * records.length + 4)
        (config (machine keep).start (pre ++ recordsBits records ++ suffix) pre.length out
          1 (UnaryTemplate.tape records.length)) = some r ∧
      r.final = config 16 (pre ++ recordsBits records ++ suffix)
        (pre.length + (recordsBits records).length) (out ++ selected keep records)
          1 (UnaryTemplate.tape records.length) ∧
      r.steps = (recordsBits records).length + 3 * records.length + 4 ∧
      r.peakTapeCells ≤ (pre ++ recordsBits records ++ suffix).length + out.length + 2 * records.length + 2 := by
  let source := pre ++ recordsBits records ++ suffix
  let next := pre.length + (recordsBits records).length
  let appended := out ++ selected keep records
  obtain ⟨phase, first, hr, hf, hs, hp⟩ := PayloadCounted.loop_run keep pre records suffix out
  obtain ⟨second, hrun, hfinal, hsteps, hpeak⟩ := reset_run source next appended records.length
  have hmid : Composition.restart first.final reset.start =
      config 0 source next appended (records.length + 1) (UnaryTemplate.tape records.length) := by
    rw [hf]
    rfl
  have hrun' : runFrom reset (records.length + 2) (Composition.restart first.final reset.start) = some second := by
    rw [hmid]
    exact hrun
  have hj := Composition.run_join (PayloadCounted.machine keep) reset
    ((recordsBits records).length + 2 * records.length + 1) (records.length + 2) _ first second hr hrun'
  have htime : ((recordsBits records).length + 2 * records.length + 1) + 1 + (records.length + 2) =
      (recordsBits records).length + 3 * records.length + 4 := by omega
  refine ⟨Composition.joinedReceipt first second, ?_, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · change Composition.rightConfig 14 second.final = _
    rw [hfinal]
    rfl
  · change first.steps + 1 + second.steps = _
    omega
  · change max first.peakTapeCells second.peakTapeCells ≤ _
    have hsel := PayloadCounted.selected_length keep records
    dsimp only [source, next, appended] at hpeak
    simp only [List.length_append] at hpeak ⊢
    simp only [List.length_append] at hp
    omega

end NearCubicWires.RepairOrdinary.PayloadRow

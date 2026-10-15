import Proof.MachineModel.OrdinaryRecordClone

/-! Actual bounded record copying followed by rank-half positioning. Both
copies and all reset tapes are retained; no caller supplies a free duplicate. -/
namespace NearCubicWires.RepairOrdinary.RecordHalf
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def position : Machine 4 5 := TapeEmbedding.machine 2 HalfPosition.machine
def machine : Machine 4 11 := Composition.machine RecordClone.machine position
def finished (word rank : List Bool) : Configuration 4 11 :=
  ⟨10, ![4 * word.length, 2 * word.length, 0, 0], RecordClone.output (word ++ rank)⟩

theorem half_run (word rank backing : List Bool) (hw : rank.length = word.length)
    (hb : backing.length ≤ 4 * word.length + 1) :
    ∃ r : ExecutionReceipt 4 11,
      run machine (20 * word.length + 10) (RecordClone.input (word ++ rank) backing) = some r ∧
      r.final = finished word rank ∧ r.steps = 20 * word.length + 10 ∧
      r.peakTapeCells ≤ 36 * word.length + 11 := by
  obtain ⟨first, hr, ht, hh, hs, hp⟩ := RecordClone.clone_run (word ++ rank) backing (by simp [hw]; omega)
  obtain ⟨base, hbase, hbf, hbs, hbp⟩ := HalfPosition.annotated_run word rank hw
  let extras : Fin 2 → List Bool := ![List.replicate (2 * (word ++ rank).length + 1) false,
    List.replicate (4 * (word ++ rank).length + 3) false]
  have he := TapeEmbedding.run_embed HalfPosition.machine (fun _ : Fin 2 => 0) extras _ _ base hbase
  let second := TapeEmbedding.receipt (fun _ : Fin 2 => 0) extras base
  have hmid : Composition.restart first.final position.start =
      TapeEmbedding.config (fun _ : Fin 2 => 0) extras
        (HalfPosition.config 0 (frame (word ++ rank)) (frame (word ++ rank)) 0 0) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, TapeEmbedding.config, HalfPosition.config, hh, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, TapeEmbedding.config, HalfPosition.config, ht,
        RecordClone.output, extras, Fin.addCases]
  have he' : runFrom position (4 * word.length + 1) (Composition.restart first.final position.start) = some second := by
    rw [hmid]
    exact he
  have hj := Composition.run_join RecordClone.machine position (8 * (word ++ rank).length + 8) (4 * word.length + 1)
    (initialConfiguration RecordClone.machine (RecordClone.input (word ++ rank) backing)) first second hr he'
  have htime : (8 * (word ++ rank).length + 8) + 1 + (4 * word.length + 1) = 20 * word.length + 10 := by
    simp only [List.length_append, hw]
    omega
  refine ⟨Composition.joinedReceipt first second, by rw [htime] at hj; exact hj, ?_, ?_, ?_⟩
  · apply configuration_ext
    · change base.final.control.natAdd 6 = (10 : Fin 11)
      rw [hbf]
      change (4 : Fin 5).natAdd 6 = (10 : Fin 11)
      decide
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeEmbedding.receipt, TapeEmbedding.config, hbf, HalfPosition.config, finished, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, second,
        TapeEmbedding.receipt, TapeEmbedding.config, hbf, HalfPosition.config, finished, RecordClone.output, extras, Fin.addCases]
  · change first.steps + 1 + base.steps = _
    simp only [List.length_append, hw] at hs
    omega
  · change max first.peakTapeCells (base.peakTapeCells + TapeEmbedding.extraCells extras) ≤ _
    simp only [List.length_append, hw] at hp
    simp [TapeEmbedding.extraCells, extras, Fin.sum_univ_succ, hw]
    omega

end NearCubicWires.RepairOrdinary.RecordHalf

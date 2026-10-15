import Proof.MachineModel.OrdinaryPayloadRow

/-! Append a unary-template-sized block of zeros, then reset only the template.
The growing matrix output cursor is never rewound. -/
namespace NearCubicWires.RepairOrdinary.ZeroBlock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (driver : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 s :=
  ⟨state, ![pos, out.length], ![driver, out]⟩
@[simp] theorem config_cells {s : ℕ} (state : Fin s) (driver : List Bool) (pos : ℕ) (out : List Bool) :
    (config state driver pos out).tapeCells = driver.length + out.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

def copy : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state scanned => if state.val = 0 then
    some (if scanned 0 then ⟨0, ![none, some false], ![.right, .right]⟩
      else ⟨1, ![none, none], ![.stay, .stay]⟩)
    else none

theorem emit_step (pre tail out : List Bool) :
    step copy (config 0 (pre ++ true :: tail) pre.length out) =
      some (config 0 (pre ++ true :: tail) (pre.length + 1) (out ++ [false])) := by
  simp [step, copy, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem stop_step (pre tail out : List Bool) :
    step copy (config 0 (pre ++ false :: tail) pre.length out) =
      some (config 1 (pre ++ false :: tail) pre.length out) := by
  simp [step, copy, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem copy_prefix (pre : List Bool) (count : ℕ) (out : List Bool) :
    Prefix copy ((pre ++ List.replicate count true ++ [false]).length + out.length + count)
      (count + 1)
      (config 0 (pre ++ List.replicate count true ++ [false]) pre.length out)
      (config 1 (pre ++ List.replicate count true ++ [false]) (pre.length + count)
        (out ++ List.replicate count false)) := by
  induction count generalizing pre out with
  | zero =>
    simpa using Prefix.step
      (by simp : (config (s := 2) 0 (pre ++ [false]) pre.length out).tapeCells ≤ (pre ++ [false]).length + out.length)
      (by rfl : copy.halted 0 = false) (stop_step pre [] out) (Prefix.refl _ (by simp))
  | succ count ih =>
    let source := pre ++ List.replicate (count + 1) true ++ [false]
    have hsource : (pre ++ [true]) ++ List.replicate count true ++ [false] = source := by
      simp [source, List.replicate_succ, List.append_assoc]
    have hout : (out ++ [false]) ++ List.replicate count false = out ++ List.replicate (count + 1) false := by
      simp [List.replicate_succ, List.append_assoc]
    have ht := ih (pre ++ [true]) (out ++ [false])
    rw [hsource, hout] at ht
    have hlen : (pre ++ [true]).length = pre.length + 1 := by simp
    rw [hlen] at ht
    have hspace : source.length + (out ++ [false]).length + count = source.length + out.length + (count + 1) := by simp; omega
    rw [hspace] at ht
    have hs : step copy (config 0 source pre.length out) = some (config 0 source (pre.length + 1) (out ++ [false])) := by
      simpa [source, List.replicate_succ, List.append_assoc] using emit_step pre (List.replicate count true ++ [false]) out
    have h := Prefix.step (by simp : (config (s := 2) 0 source pre.length out).tapeCells ≤ source.length + out.length + (count + 1))
      (by rfl : copy.halted 0 = false) hs ht
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using h

def reset : Machine 2 3 := TapeEmbedding.machine 1 UnaryTemplate.machine
def machine : Machine 2 5 := Composition.machine copy reset

theorem place (state : Fin 3) (count pos : ℕ) (out : List Bool) :
    TapeEmbedding.config ![out.length] ![out]
      (UnaryTemplate.config state (UnaryTemplate.tape count) pos) = config state (UnaryTemplate.tape count) pos out := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.config, UnaryTemplate.config, config, Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeEmbedding.config, UnaryTemplate.config, config, Fin.addCases]

theorem block_run (count : ℕ) (out : List Bool) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom machine (2 * count + 4) (config 0 (UnaryTemplate.tape count) 1 out) = some r ∧
      r.final = config 4 (UnaryTemplate.tape count) 1 (out ++ List.replicate count false) ∧
      r.steps = 2 * count + 4 ∧ r.peakTapeCells ≤ out.length + 2 * count + 2 := by
  have ht := copy_prefix [false] count out
  obtain ⟨first, hr, hf, hs, hp⟩ := ht.run (by rfl) (by simp; omega)
  simp only [List.singleton_append, List.length_singleton] at hr hf
  obtain ⟨second, hrun, hfinal, hsteps, hpeak⟩ := UnaryTemplate.reset_run count
  let appended := out ++ List.replicate count false
  have he := TapeEmbedding.run_embed UnaryTemplate.machine ![appended.length] ![appended] _ _ second hrun
  have hmid : Composition.restart first.final reset.start = config 0 (UnaryTemplate.tape count) (count + 1) appended := by
    rw [hf]
    simp only [Nat.add_comm 1 count]
    rfl
  have he' : runFrom reset (count + 2) (Composition.restart first.final reset.start) =
      some (TapeEmbedding.receipt ![appended.length] ![appended] second) := by
    rw [hmid]
    simpa only [place, reset] using he
  have hj := Composition.run_join copy reset (count + 1) (count + 2) _ first _ hr he'
  refine ⟨Composition.joinedReceipt first (TapeEmbedding.receipt ![appended.length] ![appended] second), ?_, ?_, ?_, ?_⟩
  · have htime : count + 1 + 1 + (count + 2) = 2 * count + 4 := by omega
    rw [htime] at hj
    exact hj
  · change Composition.rightConfig 2 (TapeEmbedding.config ![appended.length] ![appended] second.final) = _
    rw [hfinal, place]
    rfl
  · change first.steps + 1 + second.steps = _
    omega
  · change max first.peakTapeCells (second.peakTapeCells + TapeEmbedding.extraCells ![appended]) ≤ _
    simp only [List.length_append, List.length_singleton, List.length_replicate] at hp
    simp [TapeEmbedding.extraCells, appended]
    omega

end NearCubicWires.RepairOrdinary.ZeroBlock

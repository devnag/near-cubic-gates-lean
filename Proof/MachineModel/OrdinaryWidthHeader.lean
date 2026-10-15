import Proof.MachineModel.OrdinaryControlPrefix
import Proof.Foundations.OrdinaryStreaming

/-! Scan the first framed record and materialize two unary marks per bit.
The record stream stays on tape zero; tape four receives the actual loop
header. This fixed finite program never receives an uncharged numeric width. -/
namespace NearCubicWires.RepairOrdinary.WidthHeader
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 4) (inputMove outputMove : HeadMove) (write : Option Bool) : Action 5 4 :=
  ⟨state, fun i => if i.val = 4 then write else none,
    fun i => if i.val = 0 then inputMove else if i.val = 4 then outputMove else .stay⟩

def machine : Machine 5 4 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 3
  rule := fun state scanned =>
    if state.val = 0 then
      if scanned 0 then some (action 1 .right .stay none)
      else some (action 3 .stay .right (some false))
    else if state.val = 1 then some (action 2 .right .right (some true))
    else if state.val = 2 then some (action 0 .stay .right (some true))
    else none

def config (state : Fin 4) (input : List Bool) (position : ℕ) (output : List Bool) : Configuration 5 4 :=
  ⟨state, fun i => if i.val = 0 then position else if i.val = 4 then output.length else 0,
    fun i => if i.val = 0 then input else if i.val = 4 then output else []⟩

@[simp] theorem config_cells (state : Fin 4) (input : List Bool) (position : ℕ) (output : List Bool) :
    (config state input position output).tapeCells = input.length + output.length := by
  simp [Configuration.tapeCells, config, Fin.sum_univ_succ]

theorem marker_step (pre : List Bool) (bit : Bool) (bits suffix output : List Bool) :
    step machine (config 0 (pre ++ frame (bit :: bits) ++ suffix) pre.length output) =
      some (config 1 (pre ++ frame (bit :: bits) ++ suffix) (pre.length + 1) output) := by
  have hr : readTapeBit (pre ++ frame (bit :: bits) ++ suffix) pre.length = true := by
    simpa [frame, List.append_assoc] using Streaming.read_append pre (bit :: frame bits ++ suffix) true
  simp only [List.append_assoc] at hr
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    simp [applyAction, action]

theorem first_step (input : List Bool) (position : ℕ) (output : List Bool) :
    step machine (config 1 input position output) =
      some (config 2 input (position + 1) (output ++ [true])) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem second_step (input : List Bool) (position : ℕ) (output : List Bool) :
    step machine (config 2 input position output) =
      some (config 0 input position (output ++ [true])) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem finish_step (pre suffix output : List Bool) :
    step machine (config 0 (pre ++ frame [] ++ suffix) pre.length output) =
      some (config 3 (pre ++ frame [] ++ suffix) pre.length (output ++ [false])) := by
  have hr : readTapeBit (pre ++ frame [] ++ suffix) pre.length = false := by
    simpa [frame, List.append_assoc] using Streaming.read_append pre suffix false
  simp only [List.append_assoc] at hr
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem scan_prefix (pre bits suffix output : List Bool) :
    Prefix machine ((pre ++ frame bits ++ suffix).length + output.length + 2 * bits.length + 1)
      (3 * bits.length + 1) (config 0 (pre ++ frame bits ++ suffix) pre.length output)
      (config 3 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length)
        (output ++ List.replicate (2 * bits.length) true ++ [false])) := by
  induction bits generalizing pre output with
  | nil =>
    have hp := Prefix.step (by simp : (config 0 (pre ++ frame [] ++ suffix) pre.length output).tapeCells ≤
        (pre ++ frame [] ++ suffix).length + output.length + 2 * ([] : List Bool).length + 1)
      (by rfl : machine.halted (0 : Fin 4) = false) (finish_step pre suffix output)
      (Prefix.refl _ (by simp; omega))
    simpa using hp
  | cons bit bits ih =>
    let input := pre ++ frame (bit :: bits) ++ suffix
    let space := input.length + output.length + 2 * (bit :: bits).length + 1
    have hin : (pre ++ [true, bit]) ++ frame bits ++ suffix = input := by
      simp [input, frame, List.append_assoc]
    have hrep : List.replicate (2 * (bit :: bits).length) true =
        [true, true] ++ List.replicate (2 * bits.length) true := by
      rw [show 2 * (bit :: bits).length = 2 + 2 * bits.length by simp; omega, List.replicate_add]
      rfl
    have htail : Prefix machine space (3 * bits.length + 1)
        (config 0 input (pre.length + 2) (output ++ [true, true]))
        (config 3 input (pre.length + 2 * (bit :: bits).length)
          (output ++ List.replicate (2 * (bit :: bits).length) true ++ [false])) := by
      have hi := ih (pre ++ [true, bit]) (output ++ [true, true])
      rw [hin] at hi
      rw [hrep]
      convert hi using 1 <;>
        simp [space, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have h2 := Prefix.step (by simp [space]; omega :
        (config 2 input (pre.length + 2) (output ++ [true])).tapeCells ≤ space)
      (by rfl : machine.halted (2 : Fin 4) = false)
      (second_step input (pre.length + 2) (output ++ [true]))
      (by simpa [List.append_assoc] using htail)
    have h1 := Prefix.step (by simp [space]; omega :
        (config 1 input (pre.length + 1) output).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 4) = false)
      (first_step input (pre.length + 1) output) h2
    have h0 := Prefix.step (by simp [space]; omega :
        (config 0 input pre.length output).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 4) = false)
      (marker_step pre bit bits suffix output) h1
    convert h0 using 1 <;> simp [input, List.append_assoc, Nat.mul_add, Nat.add_assoc]

theorem scan_run (bits suffix : List Bool) :
    ∃ r : ExecutionReceipt 5 4,
      run machine (3 * bits.length + 1) (fun i => if i.val = 0 then frame bits ++ suffix else []) = some r ∧
      r.final = config 3 (frame bits ++ suffix) (2 * bits.length)
        (List.replicate (2 * bits.length) true ++ [false]) ∧
      r.steps = 3 * bits.length + 1 ∧
      r.peakTapeCells ≤ (frame bits ++ suffix).length + 2 * bits.length + 1 := by
  have hp := scan_prefix [] bits suffix []
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  have hi : initialConfiguration machine (fun i => if i.val = 0 then frame bits ++ suffix else []) =
      config 0 (frame bits ++ suffix) 0 [] := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  refine ⟨r, ?_, by simpa using hf, hs, by simpa using hb⟩
  change runFrom machine _ _ = _
  rw [hi]
  simpa using hr

end NearCubicWires.RepairOrdinary.WidthHeader

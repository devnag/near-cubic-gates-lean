import Proof.MachineModel.OrdinaryBoundedCounter

/-! First actual macro of the rank-label scan: copy one framed word without
its terminator, produce unary width marks, and preserve both stream cursors.
The subsequent macro appends the rank before closing the output record. -/
namespace NearCubicWires.RepairOrdinary.RankRecordCopy
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 3) (outputMove marksMove : HeadMove)
    (outputWrite marksWrite : Option Bool) : Action 3 3 :=
  ⟨state, fun i => if i.val = 0 then none else if i.val = 1 then outputWrite else marksWrite,
    fun i => if i.val = 0 then .right else if i.val = 1 then outputMove else marksMove⟩

def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then
      if scanned 0 then some (action 1 .right .stay (some true) none)
      else some (action 2 .stay .stay none none)
    else if state.val = 1 then some (action 0 .right .right (some (scanned 0)) (some true))
    else none

def config (state : Fin 3) (input : List Bool) (position : ℕ) (output : List Bool) (count : ℕ) :
    Configuration 3 3 :=
  ⟨state, fun i => if i.val = 0 then position else if i.val = 1 then output.length else count,
    fun i => if i.val = 0 then input else if i.val = 1 then output else List.replicate count true⟩

@[simp] theorem config_cells (state : Fin 3) (input : List Bool) (position : ℕ)
    (output : List Bool) (count : ℕ) :
    (config state input position output count).tapeCells = input.length + output.length + count := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem marker_step (pre tail output : List Bool) (count : ℕ) :
    step machine (config 0 (pre ++ true :: tail) pre.length output count) =
      some (config 1 (pre ++ true :: tail) (pre.length + 1) (output ++ [true]) count) := by
  have hr := Streaming.read_append pre tail true
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem bit_step (pre tail output : List Bool) (bit : Bool) (count : ℕ) :
    step machine (config 1 (pre ++ bit :: tail) pre.length output count) =
      some (config 0 (pre ++ bit :: tail) (pre.length + 1) (output ++ [bit]) (count + 1)) := by
  have hr := Streaming.read_append pre tail bit
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append, List.replicate_add]
    simpa using Streaming.write_append (List.replicate count true) true

theorem finish_step (pre tail output : List Bool) (count : ℕ) :
    step machine (config 0 (pre ++ false :: tail) pre.length output count) =
      some (config 2 (pre ++ false :: tail) (pre.length + 1) output count) := by
  have hr := Streaming.read_append pre tail false
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action]

theorem copy_prefix (pre bits suffix output : List Bool) (count : ℕ) :
    Prefix machine ((pre ++ frame bits ++ suffix).length + output.length + count + 3 * bits.length)
      (2 * bits.length + 1) (config 0 (pre ++ frame bits ++ suffix) pre.length output count)
      (config 2 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (output ++ Streaming.marks bits) (count + bits.length)) := by
  induction bits generalizing pre output count with
  | nil =>
    have hp := Prefix.step
      (by simp : (config 0 (pre ++ false :: suffix) pre.length output count).tapeCells ≤
        (pre ++ false :: suffix).length + output.length + count)
      (by rfl : machine.halted (0 : Fin 3) = false) (finish_step pre suffix output count)
      (Prefix.refl _ (by simp))
    simpa [frame, Streaming.marks, List.append_assoc] using hp
  | cons bit bits ih =>
    let input := pre ++ frame (bit :: bits) ++ suffix
    let space := input.length + output.length + count + 3 * (bit :: bits).length
    have hin : (pre ++ [true, bit]) ++ frame bits ++ suffix = input := by simp [input, frame, List.append_assoc]
    have htail : Prefix machine space (2 * bits.length + 1)
        (config 0 input (pre.length + 2) (output ++ [true, bit]) (count + 1))
        (config 2 input (pre.length + 2 * (bit :: bits).length + 1)
          (output ++ Streaming.marks (bit :: bits)) (count + (bit :: bits).length)) := by
      have hi := ih (pre ++ [true, bit]) (output ++ [true, bit]) (count + 1)
      rw [hin] at hi
      convert hi using 1 <;> simp [space, Streaming.marks, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    have hbit : step machine (config 1 input (pre.length + 1) (output ++ [true]) count) =
        some (config 0 input (pre.length + 2) (output ++ [true, bit]) (count + 1)) := by
      simpa [input, frame, List.append_assoc] using
        bit_step (pre ++ [true]) (frame bits ++ suffix) (output ++ [true]) bit count
    have hm : step machine (config 0 input pre.length output count) =
        some (config 1 input (pre.length + 1) (output ++ [true]) count) := by
      simpa [input, frame, List.append_assoc] using marker_step pre (bit :: frame bits ++ suffix) output count
    have h1 := Prefix.step (by simp [space]; omega :
        (config 1 input (pre.length + 1) (output ++ [true]) count).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 3) = false) hbit htail
    have h0 := Prefix.step (by simp [space] :
        (config 0 input pre.length output count).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 3) = false) hm h1
    convert h0 using 1; simp [Nat.mul_add, Nat.add_assoc]

theorem copy_run (pre bits suffix output : List Bool) :
    ∃ r : ExecutionReceipt 3 3,
      runFrom machine (2 * bits.length + 1)
        (config 0 (pre ++ frame bits ++ suffix) pre.length output 0) = some r ∧
      r.final = config 2 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (output ++ Streaming.marks bits) bits.length ∧
      r.steps = 2 * bits.length + 1 ∧
      r.peakTapeCells ≤ (pre ++ frame bits ++ suffix).length + output.length + 3 * bits.length := by
  have hp := copy_prefix pre bits suffix output 0
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, hr, by simpa using hf, hs, by simpa using hb⟩

end NearCubicWires.RepairOrdinary.RankRecordCopy

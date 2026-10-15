import Proof.MachineModel.OrdinaryCapacityEmit

/-! Load the next framed scalar into bounded retained storage and reset only
the target and counter heads. The source head advances and is never rewound.
This is the actual field-loader interface needed by the enclosing cell scan. -/
namespace NearCubicWires.RepairOrdinary.FrameLoad
open LocalBitMultitape StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 4) (sourceMove targetMove counterMove : HeadMove)
    (targetWrite counterWrite : Option Bool) : Action 3 4 :=
  ⟨state, ![none, targetWrite, counterWrite], ![sourceMove, targetMove, counterMove]⟩
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 3
  rule := fun state scanned => if state.val = 0 then
      if scanned 0 then some (action 1 .right .right .right (some true) (some true))
      else some (action 2 .right .right .stay (some false) (some true))
    else if state.val = 1 then some (action 0 .right .right .right (some (scanned 0)) (some true))
    else if state.val = 2 then
      if scanned 2 then some (action 2 .stay .left .left none (some false))
      else some (action 3 .stay .stay .stay none none)
    else none

def scan (state : Fin 4) (source : List Bool) (position : ℕ) (out backing : List Bool) : Configuration 3 4 :=
  ⟨state, ![position, out.length, out.length],
    ![source, overlay out backing, List.replicate out.length true]⟩
def reset (state : Fin 4) (source : List Bool) (position : ℕ) (target : List Bool)
    (remaining erased : ℕ) : Configuration 3 4 :=
  ⟨state, ![position, remaining, remaining - 1],
    ![source, target, List.replicate remaining true ++ List.replicate erased false]⟩

@[simp] theorem scan_cells (state : Fin 4) (source : List Bool) (position : ℕ) (out backing : List Bool) :
    (scan state source position out backing).tapeCells = source.length + max out.length backing.length + out.length := by
  simp [scan, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]
@[simp] theorem reset_cells (state : Fin 4) (source : List Bool) (position : ℕ) (target : List Bool)
    (remaining erased : ℕ) :
    (reset state source position target remaining erased).tapeCells = source.length + target.length + remaining + erased := by
  simp [reset, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]

theorem marker_step (pre tail out backing : List Bool) :
    step machine (scan 0 (pre ++ true :: tail) pre.length out backing) =
      some (scan 1 (pre ++ true :: tail) (pre.length + 1) (out ++ [true]) backing) := by
  have hr := Streaming.read_append pre tail true
  simp [step, machine, scan, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, overlay_write, List.replicate_add]
    simpa using Streaming.write_append (List.replicate out.length true) true

theorem bit_step (pre tail out backing : List Bool) (bit : Bool) :
    step machine (scan 1 (pre ++ bit :: tail) pre.length out backing) =
      some (scan 0 (pre ++ bit :: tail) (pre.length + 1) (out ++ [bit]) backing) := by
  have hr := Streaming.read_append pre tail bit
  simp [step, machine, scan, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, overlay_write, List.replicate_add]
    simpa using Streaming.write_append (List.replicate out.length true) true

theorem delimiter_step (pre tail out backing : List Bool) :
    step machine (scan 0 (pre ++ false :: tail) pre.length out backing) =
      some (reset 2 (pre ++ false :: tail) (pre.length + 1) (overlay (out ++ [false]) backing)
        (out.length + 1) 0) := by
  have hr := Streaming.read_append pre tail false
  simp [step, machine, scan, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply, reset]
  · funext i
    fin_cases i <;> simp [applyAction, action, overlay_write, reset, List.replicate_add]
    simpa using Streaming.write_append (List.replicate out.length true) true

theorem rewind_step (source target : List Bool) (position remaining erased : ℕ) :
    step machine (reset 2 source position target (remaining + 1) erased) =
      some (reset 2 source position target remaining (erased + 1)) := by
  simp [step, machine, reset, Configuration.scanned, Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.erase_counter]

theorem stop_step (source target : List Bool) (position erased : ℕ) :
    step machine (reset 2 source position target 0 erased) = some (reset 3 source position target 0 erased) := by
  simp [step, machine, reset, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action]

theorem reset_prefix (source target : List Bool) (position remaining erased : ℕ) :
    Prefix machine (source.length + target.length + remaining + erased) (remaining + 1)
      (reset 2 source position target remaining erased) (reset 3 source position target 0 (remaining + erased)) := by
  induction remaining generalizing erased with
  | zero =>
    simpa using Prefix.step (by simp : (reset 2 source position target 0 erased).tapeCells ≤
      source.length + target.length + erased) (by rfl : machine.halted (2 : Fin 4) = false)
      (stop_step source target position erased) (Prefix.refl _ (by simp))
  | succ remaining ih =>
    have htail := ih (erased + 1)
    have hp := Prefix.step (by simp; omega : (reset 2 source position target (remaining + 1) erased).tapeCells ≤
      source.length + target.length + remaining + (erased + 1))
      (by rfl : machine.halted (2 : Fin 4) = false) (rewind_step source target position remaining erased) htail
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem scan_prefix (pre bits suffix out backing : List Bool) :
    Prefix machine ((pre ++ frame bits ++ suffix).length + backing.length + 2 * (out.length + (frame bits).length))
      (2 * bits.length + 1) (scan 0 (pre ++ frame bits ++ suffix) pre.length out backing)
      (reset 2 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (overlay (out ++ frame bits) backing) (out.length + 2 * bits.length + 1) 0) := by
  induction bits generalizing pre out with
  | nil =>
    have hp := Prefix.step (by simp; omega : (scan 0 (pre ++ false :: suffix) pre.length out backing).tapeCells ≤
      (pre ++ false :: suffix).length + backing.length + 2 * (out.length + 1))
      (by rfl : machine.halted (0 : Fin 4) = false) (delimiter_step pre suffix out backing)
      (Prefix.refl _ (by simp; omega))
    simpa [frame] using hp
  | cons bit bits ih =>
    let source := pre ++ frame (bit :: bits) ++ suffix
    let space := source.length + backing.length + 2 * (out.length + (frame (bit :: bits)).length)
    have he : (pre ++ [true, bit]) ++ frame bits ++ suffix = source := by simp [source, frame, List.append_assoc]
    have htail : Prefix machine space (2 * bits.length + 1)
        (scan 0 source (pre.length + 2) (out ++ [true, bit]) backing)
        (reset 2 source (pre.length + 2 * (bit :: bits).length + 1)
          (overlay (out ++ frame (bit :: bits)) backing) (out.length + 2 * (bit :: bits).length + 1) 0) := by
      have hi := ih (pre ++ [true, bit]) (out ++ [true, bit])
      rw [he] at hi
      convert hi using 1 <;> simp [space, frame, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    have hbit := bit_step (pre ++ [true]) (frame bits ++ suffix) (out ++ [true]) backing bit
    have h1 := Prefix.step (by simp [space, source]; omega :
        (scan 1 source (pre.length + 1) (out ++ [true]) backing).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 4) = false)
      (by simpa [source, frame, List.append_assoc] using hbit)
      (by simpa [source, frame, List.append_assoc, Nat.add_assoc] using htail)
    have h0 := Prefix.step (by simp [space, source]; omega : (scan 0 source pre.length out backing).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 4) = false)
      (by simpa [source, frame, List.append_assoc] using marker_step pre (bit :: frame bits ++ suffix) out backing) h1
    convert h0 using 1 <;> simp [frame, List.append_assoc, Nat.mul_add, Nat.add_assoc]

theorem load_run (pre bits suffix backing : List Bool) (hb : backing.length ≤ 2 * bits.length + 1) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom machine (4 * bits.length + 3)
        (scan 0 (pre ++ frame bits ++ suffix) pre.length [] backing) = some r ∧
      r.final = reset 3 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (frame bits) 0 (2 * bits.length + 1) ∧
      r.steps = 4 * bits.length + 3 ∧
      r.peakTapeCells ≤ (pre ++ frame bits ++ suffix).length + 6 * bits.length + 3 := by
  have hover : overlay (frame bits) backing = frame bits := by
    simp [overlay, List.drop_eq_nil_of_le (by simpa using hb)]
  have hscan := scan_prefix pre bits suffix [] backing
  simp only [List.nil_append, List.length_nil, Nat.zero_add, frame_length, hover] at hscan
  have hreset := reset_prefix (pre ++ frame bits ++ suffix) (frame bits)
    (pre.length + 2 * bits.length + 1) (2 * bits.length + 1) 0
  let space := (pre ++ frame bits ++ suffix).length + 6 * bits.length + 3
  have hs := hscan.enlarge (large := space) (by dsimp [space]; omega)
  have hr := hreset.enlarge (large := space) (by dsimp [space]; simp; omega)
  have hj := hs.trans hr
  obtain ⟨r, hrun, hf, hsteps, hp⟩ := hj.run (by rfl) (by simp [space]; omega)
  refine ⟨r, ?_, by simpa using hf, ?_, hp⟩
  · have hbudget : (2 * bits.length + 1) + (2 * bits.length + 1 + 1) = 4 * bits.length + 3 := by omega
    rw [hbudget] at hrun
    exact hrun
  · omega

end NearCubicWires.RepairOrdinary.FrameLoad

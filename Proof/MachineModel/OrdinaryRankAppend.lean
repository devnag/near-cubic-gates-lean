import Proof.MachineModel.OrdinaryRankRecordCopy

/-! Consume unary width marks backwards while appending the rank's framed
bits. The output append head is preserved and a fresh rewind certificate is
written for the scalar rank tape. -/
namespace NearCubicWires.RepairOrdinary.RankAppend
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 3) (rankMove marksMove savedMove : HeadMove)
    (outputBit : Bool) (marksWrite savedWrite : Option Bool) : Action 4 3 :=
  ⟨state, fun i => if i.val = 0 then none else if i.val = 1 then some outputBit
      else if i.val = 2 then marksWrite else savedWrite,
    fun i => if i.val = 0 then rankMove else if i.val = 1 then .right
      else if i.val = 2 then marksMove else savedMove⟩

def machine : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then
      if scanned 2 then some (action 1 .stay .left .stay true (some false) none)
      else some (action 2 .stay .stay .stay false none none)
    else if state.val = 1 then some (action 0 .right .stay .right (scanned 0) none (some true))
    else none

def config (state : Fin 3) (rank : List Bool) (position : ℕ) (output : List Bool)
    (remaining erased saved : ℕ) : Configuration 4 3 :=
  ⟨state, fun i => if i.val = 0 then position else if i.val = 1 then output.length
      else if i.val = 2 then remaining - 1 else saved,
    fun i => if i.val = 0 then rank else if i.val = 1 then output
      else if i.val = 2 then List.replicate remaining true ++ List.replicate erased false
      else List.replicate saved true⟩

@[simp] theorem config_cells (state : Fin 3) (rank : List Bool) (position : ℕ)
    (output : List Bool) (remaining erased saved : ℕ) :
    (config state rank position output remaining erased saved).tapeCells =
      rank.length + output.length + remaining + erased + saved := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem marker_step (rank : List Bool) (position : ℕ) (output : List Bool) (remaining erased saved : ℕ) :
    step machine (config 0 rank position output (remaining + 1) erased saved) =
      some (config 1 rank position (output ++ [true]) remaining (erased + 1) saved) := by
  simp [step, machine, config, Configuration.scanned, Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append, Streaming.erase_counter]

theorem bit_step (rank : List Bool) (position : ℕ) (output : List Bool) (remaining erased saved : ℕ)
    (bit : Bool) (hr : readTapeBit rank position = bit) :
    step machine (config 1 rank position output remaining erased saved) =
      some (config 0 rank (position + 1) (output ++ [bit]) remaining erased (saved + 1)) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append, List.replicate_add]
    simpa using Streaming.write_append (List.replicate saved true) true

theorem finish_step (rank : List Bool) (position : ℕ) (output : List Bool) (erased saved : ℕ) :
    step machine (config 0 rank position output 0 erased saved) =
      some (config 2 rank position (output ++ [false]) 0 erased saved) := by
  simp [step, machine, config, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem append_prefix (pre bits output : List Bool) :
    Prefix machine (3 * (pre.length + bits.length) + output.length + 2 * bits.length + 1)
      (2 * bits.length + 1)
      (config 0 (pre ++ bits) pre.length output bits.length pre.length pre.length)
      (config 2 (pre ++ bits) (pre.length + bits.length)
        (output ++ Streaming.marks bits ++ [false]) 0 (pre.length + bits.length) (pre.length + bits.length)) := by
  induction bits generalizing pre output with
  | nil =>
    have hp := Prefix.step (by simp; omega :
        (config 0 pre pre.length output 0 pre.length pre.length).tapeCells ≤ 3 * pre.length + output.length + 1)
      (by rfl : machine.halted (0 : Fin 3) = false) (finish_step pre pre.length output pre.length pre.length)
      (Prefix.refl _ (by simp; omega))
    simpa [Streaming.marks] using hp
  | cons bit bits ih =>
    let rank := pre ++ bit :: bits
    let space := 3 * (pre.length + (bit :: bits).length) + output.length + 2 * (bit :: bits).length + 1
    have htail : Prefix machine space (2 * bits.length + 1)
        (config 0 rank (pre.length + 1) (output ++ [true, bit]) bits.length (pre.length + 1) (pre.length + 1))
        (config 2 rank (pre.length + (bit :: bits).length)
          (output ++ Streaming.marks (bit :: bits) ++ [false]) 0
          (pre.length + (bit :: bits).length) (pre.length + (bit :: bits).length)) := by
      have hi := ih (pre ++ [bit]) (output ++ [true, bit])
      convert hi using 1 <;> simp [space, rank, Streaming.marks, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hbit := bit_step rank pre.length (output ++ [true]) bits.length (pre.length + 1) pre.length bit
      (Streaming.read_append pre bits bit)
    have h1 := Prefix.step (by simp [space, rank]; omega :
        (config 1 rank pre.length (output ++ [true]) bits.length (pre.length + 1) pre.length).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 3) = false) hbit
      (by simpa [List.append_assoc] using htail)
    have h0 := Prefix.step (by simp [space, rank]; omega :
        (config 0 rank pre.length output (bits.length + 1) pre.length pre.length).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 3) = false)
      (marker_step rank pre.length output bits.length pre.length pre.length) h1
    convert h0 using 1 <;> simp [rank, Nat.mul_add, Nat.add_assoc]

theorem append_run (bits output : List Bool) :
    ∃ r : ExecutionReceipt 4 3,
      runFrom machine (2 * bits.length + 1) (config 0 bits 0 output bits.length 0 0) = some r ∧
      r.final = config 2 bits bits.length (output ++ Streaming.marks bits ++ [false]) 0 bits.length bits.length ∧
      r.steps = 2 * bits.length + 1 ∧ r.peakTapeCells ≤ 5 * bits.length + output.length + 1 := by
  have hp := append_prefix [] bits output
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  refine ⟨r, by simpa using hr, by simpa using hf, hs, ?_⟩
  simp only [List.length_nil, Nat.zero_add] at hb
  omega

end NearCubicWires.RepairOrdinary.RankAppend

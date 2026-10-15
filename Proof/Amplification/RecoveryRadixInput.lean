import Proof.Amplification.RecoverySubtract
import Proof.MachineModel.OrdinaryRewindWorkspace

/-! Paid little-endian to even-length most-significant-first input preparation.
The first pass emits one leading zero per input bit and records two unary
marks. The reverse pass consumes those marks while copying the input bits
backwards. Thus no parity test or numeric loop bound is supplied for free. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRadixInput
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def framePrefix : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: framePrefix bs

@[simp] theorem prefix_length (bits : List Bool) : (framePrefix bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [framePrefix, ih]; omega

theorem prefix_append (left right : List Bool) : framePrefix (left ++ right) = framePrefix left ++ framePrefix right := by
  induction left with
  | nil => rfl
  | cons b bs ih => simp [framePrefix, ih]

theorem frame_append (left right : List Bool) : frame (left ++ right) = framePrefix left ++ frame right := by
  induction left with
  | nil => rfl
  | cons b bs ih => simp [framePrefix, frame, ih]

def action (state : Fin 6) (inputMove outputMove counterMove : HeadMove)
    (output counter : Option Bool) : Action 3 6 :=
  ⟨state, ![none, output, counter], ![inputMove, outputMove, counterMove]⟩

def bitState (bit : Bool) : Fin 6 := if bit then 4 else 3

def machine : Machine 3 6 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 5
  rule := fun state scanned =>
    if state.val = 0 then
      if scanned 0 then some (action 1 .right .right .right (some true) (some true))
      else some (action 2 .left .stay .left none none)
    else if state.val = 1 then some (action 0 .right .right .right (some false) (some true))
    else if state.val = 2 then
      if scanned 2 then some (action (bitState (scanned 0)) .left .right .left (some true) (some false))
      else some (action 5 .stay .right .stay (some false) none)
    else if state.val < 5 then some (action 2 .left .right .left (some (state.val == 4)) (some false))
    else none

def forward (state : Fin 6) (input : List Bool) (position : Nat) (out : List Bool) : Configuration 3 6 :=
  ⟨state, ![position, out.length, position], ![input, out, List.replicate position true]⟩

def reverse (state : Fin 6) (input : List Bool) (position : Nat) (out : List Bool)
    (remaining erased : Nat) : Configuration 3 6 :=
  ⟨state, ![position, out.length, remaining - 1],
    ![input, out, List.replicate remaining true ++ List.replicate erased false]⟩

@[simp] theorem forward_cells (state : Fin 6) (input : List Bool) (position : Nat) (out : List Bool) :
    (forward state input position out).tapeCells = input.length + out.length + position := by
  simp [forward, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

@[simp] theorem reverse_cells (state : Fin 6) (input : List Bool) (position : Nat) (out : List Bool)
    (remaining erased : Nat) :
    (reverse state input position out remaining erased).tapeCells =
      input.length + out.length + remaining + erased := by
  simp [reverse, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

@[simp] private theorem write_marks (position : Nat) :
    writeTapeBit (List.replicate position true) position true = List.replicate (position + 1) true := by
  simpa [List.replicate_add] using Streaming.write_append (List.replicate position true) true

theorem forward_marker (input : List Bool) (position : Nat) (out : List Bool)
    (hread : readTapeBit input position = true) :
    step machine (forward 0 input position out) =
      some (forward 1 input (position + 1) (out ++ [true])) := by
  simp [step, machine, forward, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append, List.replicate_add]

theorem forward_bit (input : List Bool) (position : Nat) (out : List Bool) :
    step machine (forward 1 input position out) =
      some (forward 0 input (position + 1) (out ++ [false])) := by
  simp [step, machine, forward]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append, List.replicate_add]

theorem bridge_step (input : List Bool) (position : Nat) (out : List Bool)
    (hread : readTapeBit input position = false) :
    step machine (forward 0 input position out) =
      some (reverse 2 input (position - 1) out position 0) := by
  simp [step, machine, forward, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, reverse, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, reverse]

theorem reverse_marker (input : List Bool) (position : Nat) (out : List Bool)
    (remaining erased : Nat) (bit : Bool) (hread : readTapeBit input position = bit) :
    step machine (reverse 2 input position out (remaining + 1) erased) =
      some (reverse (bitState bit) input (position - 1) (out ++ [true]) remaining (erased + 1)) := by
  simp [step, machine, reverse, Configuration.scanned, hread, Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append, Streaming.erase_counter]

theorem reverse_bit (input : List Bool) (position : Nat) (out : List Bool)
    (remaining erased : Nat) (bit : Bool) :
    step machine (reverse (bitState bit) input position out (remaining + 1) erased) =
      some (reverse 2 input (position - 1) (out ++ [bit]) remaining (erased + 1)) := by
  cases bit <;> simp [step, machine, reverse, bitState]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction, action, HeadMove.apply, Streaming.write_append, Streaming.erase_counter])

theorem finish_step (input out : List Bool) (erased : Nat) :
    step machine (reverse 2 input 0 out 0 erased) =
      some (reverse 5 input 0 (out ++ [false]) 0 erased) := by
  simp [step, machine, reverse, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem forward_prefix (pre bits out : List Bool) :
    Prefix machine ((framePrefix pre ++ frame bits).length + out.length + 2 * pre.length + 4 * bits.length)
      (2 * bits.length)
      (forward 0 (framePrefix pre ++ frame bits) (2 * pre.length) out)
      (forward 0 (framePrefix pre ++ frame bits) (2 * pre.length + 2 * bits.length)
        (out ++ framePrefix (List.replicate bits.length false))) := by
  induction bits generalizing pre out with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, framePrefix, List.append_nil, Nat.mul_zero, Nat.add_zero]
    exact Prefix.refl _ (by simp)
  | cons bit bits ih =>
    let input := framePrefix pre ++ frame (bit :: bits)
    let space := input.length + out.length + 2 * pre.length + 4 * (bit :: bits).length
    have hin : framePrefix (pre ++ [bit]) ++ frame bits = input := by
      simp [prefix_append, framePrefix, frame, input, List.append_assoc]
    have ht := ih (pre ++ [bit]) (out ++ [true, false])
    rw [hin] at ht
    have ht' : Prefix machine space (2 * bits.length)
        (forward 0 input (2 * pre.length + 2) (out ++ [true, false]))
        (forward 0 input (2 * pre.length + 2 * (bit :: bits).length)
          (out ++ framePrefix (List.replicate (bit :: bits).length false))) := by
      convert ht using 1 <;>
        simp [space, framePrefix, List.replicate_succ, List.append_assoc, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    have hread : readTapeBit input (2 * pre.length) = true := by
      simpa [input, frame, List.append_assoc] using
        Streaming.read_append (framePrefix pre) (bit :: frame bits) true
    have hbit := Prefix.step (by simp [space]; omega :
        (forward 1 input (2 * pre.length + 1) (out ++ [true])).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 6) = false)
      (forward_bit input (2 * pre.length + 1) (out ++ [true]))
      (by simpa [List.append_assoc, Nat.add_assoc] using ht')
    have hmarker := Prefix.step (by simp [space] :
        (forward 0 input (2 * pre.length) out).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 6) = false) (forward_marker input _ out hread) hbit
    convert hmarker using 1 <;> simp [input, Nat.mul_add]

theorem reverse_prefix (bits done out : List Bool) :
    Prefix machine ((frame (bits.reverse ++ done)).length + out.length + 4 * bits.length + 2 * done.length + 1)
      (2 * bits.length + 1)
      (reverse 2 (frame (bits.reverse ++ done)) (2 * bits.length - 1) out (2 * bits.length) (2 * done.length))
      (reverse 5 (frame (bits.reverse ++ done)) 0 (out ++ frame bits) 0
        (2 * bits.length + 2 * done.length)) := by
  induction bits generalizing done out with
  | nil =>
    simpa [frame] using Prefix.step
      (by simp : (reverse 2 (frame done) 0 out 0 (2 * done.length)).tapeCells ≤
        (frame done).length + out.length + 2 * done.length + 1)
      (by rfl : machine.halted (2 : Fin 6) = false) (finish_step (frame done) out _)
      (Prefix.refl _ (by simp; omega))
  | cons bit bits ih =>
    let input := frame ((bit :: bits).reverse ++ done)
    let space := input.length + out.length + 4 * (bit :: bits).length + 2 * done.length + 1
    have hin : frame (bits.reverse ++ bit :: done) = input := by
      simp [input, List.reverse_cons, List.append_assoc]
    have ht := ih (bit :: done) (out ++ [true, bit])
    rw [hin] at ht
    have ht' : Prefix machine space (2 * bits.length + 1)
        (reverse 2 input (2 * bits.length - 1) (out ++ [true, bit])
          (2 * bits.length) (2 * done.length + 2))
        (reverse 5 input 0 (out ++ frame (bit :: bits)) 0
          (2 * (bit :: bits).length + 2 * done.length)) := by
      convert ht using 1 <;> simp [space, frame, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
    have hread : readTapeBit input (2 * bits.length + 1) = bit := by
      have h := Streaming.read_append (framePrefix bits.reverse ++ [true]) (frame done) bit
      simpa [← hin, frame_append, frame, List.append_assoc] using h
    have hb := reverse_bit input (2 * bits.length) (out ++ [true])
      (2 * bits.length) (2 * done.length + 1) bit
    have hp := Prefix.step (by simp [space]; omega :
        (reverse (bitState bit) input (2 * bits.length) (out ++ [true])
          (2 * bits.length + 1) (2 * done.length + 1)).tapeCells ≤ space)
      (by cases bit <;> rfl) hb
      (by simpa [List.append_assoc, Nat.add_assoc] using ht')
    have hm := reverse_marker input (2 * bits.length + 1) out
      (2 * bits.length + 1) (2 * done.length) bit hread
    have hp' := Prefix.step (by simp [space]; omega :
        (reverse 2 input (2 * bits.length + 1) out (2 * bits.length + 2) (2 * done.length)).tapeCells ≤ space)
      (by rfl : machine.halted (2 : Fin 6) = false) hm (by simpa using hp)
    convert hp' using 1 <;> simp [input, Nat.mul_add]

def prepared (bits : List Bool) : List Bool := List.replicate bits.length false ++ bits.reverse

theorem prepared_length (bits : List Bool) : (prepared bits).length = 2 * bits.length := by
  simp [prepared]; omega

theorem prepare_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 3 6,
      run machine (4 * bits.length + 2) (fun i => if i.val = 0 then frame bits else []) = some r ∧
      r.final = reverse 5 (frame bits) 0 (frame (prepared bits)) 0 (2 * bits.length) ∧
      r.steps = 4 * bits.length + 2 ∧ r.peakTapeCells ≤ 8 * bits.length + 2 := by
  let space := 8 * bits.length + 2
  have hforward := (forward_prefix [] bits []).enlarge (large := space) (by simp [space]; omega)
  have hreverse := (reverse_prefix bits.reverse [] (framePrefix (List.replicate bits.length false))).enlarge
    (large := space) (by simp [space]; omega)
  have hread : readTapeBit (frame bits) (2 * bits.length) = false := by
    have he := frame_append bits []
    simp only [List.append_nil, frame] at he
    rw [he]
    simpa using Streaming.read_append (framePrefix bits) [] false
  have hbridge := Prefix.step (by simp [space]; omega :
      (forward 0 (frame bits) (2 * bits.length) (framePrefix (List.replicate bits.length false))).tapeCells ≤ space)
    (by rfl : machine.halted (0 : Fin 6) = false)
    (bridge_step (frame bits) _ _ hread)
    (by simpa using hreverse)
  have hj := (by simpa [framePrefix] using hforward : Prefix machine space (2 * bits.length)
      (forward 0 (frame bits) 0 [])
      (forward 0 (frame bits) (2 * bits.length) (framePrefix (List.replicate bits.length false)))).trans hbridge
  obtain ⟨r, hr, hf, hs, hpeak⟩ := hj.run (by rfl) (by simp [space]; omega)
  have hi : initialConfiguration machine (fun i => if i.val = 0 then frame bits else []) =
      forward 0 (frame bits) 0 [] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  refine ⟨r, ?_, ?_, ?_, hpeak⟩
  · change runFrom machine _ _ = _
    rw [hi]
    rw [show 4 * bits.length + 2 = 2 * bits.length + (2 * bits.length + 1 + 1) by omega]
    exact hr
  · simpa [prepared, frame_append] using hf
  · omega

end NearCubicWires.RepairOrdinary.RecoveryRadixInput

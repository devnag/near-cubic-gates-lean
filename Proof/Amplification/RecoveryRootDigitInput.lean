import Proof.Amplification.RecoveryRootInitialization

/-! A four-step read of a framed radix-4 digit. The two input bits are kept
in finite control, and the stream cursor remains advanced for the next round. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootDigitInput
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def highState (hi : Bool) : Fin 11 := if hi then 3 else 2
def lowState (hi : Bool) : Fin 11 := if hi then 5 else 4
def finalState (lo hi : Bool) : Fin 11 := ⟨6 + lo.toNat + 2 * hi.toNat, by cases lo <;> cases hi <;> decide⟩
def action (q : Fin 11) (move : HeadMove) : Action 1 11 := ⟨q, fun _ => none, fun _ => move⟩
def machine : Machine 1 11 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (6 ≤ q.val)
  rule := fun q scanned =>
    if q.val = 0 then
      if scanned 0 then some (action 1 .right) else some (action 10 .stay)
    else if q.val = 1 then some (action (highState (scanned 0)) .right)
    else if q.val < 4 then some (action (lowState (q.val == 3)) .right)
    else if q.val < 6 then some (action (finalState (scanned 0) (q.val == 5)) .right)
    else none

def config (q : Fin 11) (input : List Bool) (position : Nat) : Configuration 1 11 :=
  ⟨q, fun _ => position, fun _ => input⟩

theorem action_config (q next : Fin 11) (input : List Bool) (position : Nat) (move : HeadMove) :
    applyAction (config q input position) (action next move) = config next input (move.apply position) := rfl

theorem digit_run (pre rest : List Bool) (lo hi : Bool) :
    ∃ r : ExecutionReceipt 1 11,
      runFrom machine 4 (config 0 (pre ++ frame (hi :: lo :: rest)) pre.length) = some r ∧
      r.final = config (finalState lo hi) (pre ++ frame (hi :: lo :: rest)) (pre.length + 4) ∧
      r.steps = 4 := by
  let input := pre ++ frame (hi :: lo :: rest)
  have h0 : readTapeBit input pre.length = true := by
    simpa [input, frame] using Streaming.read_append pre (hi :: frame (lo :: rest)) true
  have h1 : readTapeBit input (pre.length + 1) = hi := by
    simpa [input, frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame (lo :: rest)) hi
  have h3 : readTapeBit input (pre.length + 3) = lo := by
    simpa [input, frame, List.append_assoc] using Streaming.read_append (pre ++ [true, hi, true]) (frame rest) lo
  have a : step machine (config 0 input pre.length) = some (config 1 input (pre.length + 1)) := by
    simp only [step, config, machine, Configuration.scanned, h0]
    rfl
  have b : step machine (config 1 input (pre.length + 1)) = some (config (highState hi) input (pre.length + 2)) := by
    simp only [step, config, machine, Configuration.scanned, h1]
    rfl
  have c : step machine (config (highState hi) input (pre.length + 2)) =
      some (config (lowState hi) input (pre.length + 3)) := by
    cases hi <;> simp [step, machine, highState, lowState, config, applyAction, action, HeadMove.apply, Nat.add_assoc]
  have d : step machine (config (lowState hi) input (pre.length + 3)) =
      some (config (finalState lo hi) input (pre.length + 4)) := by
    cases hi <;> simp [step, machine, lowState, config, Configuration.scanned, h3,
      applyAction, action, HeadMove.apply, Nat.add_assoc]
  have hp := Timed.step (by rfl) a (Timed.step (by rfl) b
    (Timed.step (by cases hi <;> rfl) c (Timed.step (by cases hi <;> rfl) d
      (Timed.refl machine (config (finalState lo hi) input (pre.length + 4))))))
  exact hp.run (by cases lo <;> cases hi <;> rfl)

theorem finish_run (pre : List Bool) :
    ∃ r : ExecutionReceipt 1 11,
      runFrom machine 1 (config 0 (pre ++ [false]) pre.length) = some r ∧
      r.final = config 10 (pre ++ [false]) pre.length ∧ r.steps = 1 := by
  have hread : readTapeBit (pre ++ [false]) pre.length = false := by
    simpa using Streaming.read_append pre [] false
  have hs : step machine (config 0 (pre ++ [false]) pre.length) = some (config 10 (pre ++ [false]) pre.length) := by
    simp only [step, config, machine, Configuration.scanned, hread]
    rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryRootDigitInput

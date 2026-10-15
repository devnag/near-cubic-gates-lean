import Proof.MachineModel.OrdinaryPayloadField

/-! Reusable unary dimension templates. A leading false sentinel permits an
actual linear return scan without erasing or regenerating the template. -/
namespace NearCubicWires.RepairOrdinary.UnaryTemplate
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tape (count : ℕ) : List Bool := false :: (List.replicate count true ++ [false])
def config (state : Fin 3) (source : List Bool) (pos : ℕ) : Configuration 1 3 :=
  ⟨state, fun _ => pos, fun _ => source⟩
def action (state : Fin 3) (move : HeadMove) : Action 1 3 := ⟨state, fun _ => none, fun _ => move⟩
def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then some (action 1 .left)
    else if state.val = 1 then some (if scanned 0 then action 1 .left else action 2 .right)
    else none

@[simp] theorem config_cells (state : Fin 3) (source : List Bool) (pos : ℕ) :
    (config state source pos).tapeCells = source.length := by simp [config, Configuration.tapeCells]
@[simp] theorem tape_length (count : ℕ) : (tape count).length = count + 2 := by simp [tape]
@[simp] theorem tape_zero (count : ℕ) : readTapeBit (tape count) 0 = false := rfl

@[simp] theorem tape_end (count : ℕ) : readTapeBit (tape count) (count + 1) = false := by
  simpa [tape] using Streaming.read_append (false :: List.replicate count true) [] false

theorem tape_mark (count k : ℕ) (hk : k < count) : readTapeBit (tape count) (k + 1) = true := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ count by omega)
  have h := Streaming.read_append (false :: List.replicate k true) (List.replicate rest true ++ [false]) true
  simpa [tape, List.replicate_add, List.append_assoc] using h

theorem start_step (source : List Bool) (count : ℕ) :
    step machine (config 0 source (count + 1)) = some (config 1 source count) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem left_step (source : List Bool) (count : ℕ) (hm : readTapeBit source (count + 1) = true) :
    step machine (config 1 source (count + 1)) = some (config 1 source count) := by
  simp [step, machine, config, Configuration.scanned, hm]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem stop_step (source : List Bool) (hz : readTapeBit source 0 = false) :
    step machine (config 1 source 0) = some (config 2 source 1) := by
  simp [step, machine, config, Configuration.scanned, hz]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem return_prefix (source : List Bool) (count : ℕ) (hz : readTapeBit source 0 = false)
    (hm : ∀ k < count, readTapeBit source (k + 1) = true) :
    Prefix machine source.length (count + 1) (config 1 source count) (config 2 source 1) := by
  induction count with
  | zero =>
    exact Prefix.step (by simp) (by rfl) (stop_step source hz) (Prefix.refl _ (by simp))
  | succ count ih =>
    exact Prefix.step (by simp) (by rfl) (left_step source count (hm count (by omega)))
      (ih (fun k hk => hm k (by omega)))

theorem reset_run (count : ℕ) :
    ∃ r : ExecutionReceipt 1 3,
      runFrom machine (count + 2) (config 0 (tape count) (count + 1)) = some r ∧
      r.final = config 2 (tape count) 1 ∧ r.steps = count + 2 ∧ r.peakTapeCells ≤ count + 2 := by
  have hp := return_prefix (tape count) count (tape_zero count) (tape_mark count)
  have h := Prefix.step (by simp : (config 0 (tape count) (count + 1)).tapeCells ≤ (tape count).length)
    (by rfl : machine.halted (0 : Fin 3) = false) (start_step (tape count) count) hp
  obtain ⟨r, hr, hf, hs, hb⟩ := h.run (by rfl) (by simp)
  exact ⟨r, by simpa [Nat.add_assoc] using hr, hf, by omega, by simpa using hb⟩

end NearCubicWires.RepairOrdinary.UnaryTemplate

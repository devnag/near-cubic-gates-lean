import Proof.MachineModel.OrdinarySignedSortKey
import Proof.MachineModel.OrdinaryRewindWorkspace

/-! Ordinary scalar counter step for sequential rank/bucket scans. A carry
walk changes only scanned cells; the retained auxiliary counter pays the
rewind. The bound depends on scalar width, not the surrounding table size. -/
namespace NearCubicWires.RepairOrdinary.BinaryIncrement
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state scanned => if state.val = 0 then
    some ⟨if scanned 0 then 0 else 1, fun _ => some (!scanned 0),
      fun _ => if scanned 0 then .right else .stay⟩ else none

def config (state : Fin 2) (bits : List Bool) (position : ℕ) : Configuration 1 2 :=
  ⟨state, fun _ => position, fun _ => bits⟩

@[simp] theorem config_cells (state : Fin 2) (bits : List Bool) (position : ℕ) :
    (config state bits position).tapeCells = bits.length := by
  simp [config, Configuration.tapeCells]

theorem write_prefix (pre tail : List Bool) (old bit : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length bit = pre ++ bit :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem carry_step (pre tail : List Bool) :
    step machine (config 0 (pre ++ true :: tail) pre.length) =
      some (config 0 (pre ++ false :: tail) (pre.length + 1)) := by
  have hr := Streaming.read_append pre tail true
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact write_prefix pre tail true false

theorem stop_step (pre tail : List Bool) :
    step machine (config 0 (pre ++ false :: tail) pre.length) =
      some (config 1 (pre ++ true :: tail) pre.length) := by
  have hr := Streaming.read_append pre tail false
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact write_prefix pre tail false true

theorem carry_prefix (count : ℕ) (pre tail : List Bool) :
    Prefix machine (pre.length + count + 1 + tail.length) (count + 1)
      (config 0 (pre ++ List.replicate count true ++ false :: tail) pre.length)
      (config 1 (pre ++ List.replicate count false ++ true :: tail) (pre.length + count)) := by
  induction count generalizing pre with
  | zero =>
    have hp := Prefix.step
      (by simp; omega : (config 0 (pre ++ false :: tail) pre.length).tapeCells ≤
        pre.length + 0 + 1 + tail.length)
      (by rfl : machine.halted (0 : Fin 2) = false) (stop_step pre tail)
      (Prefix.refl _ (by simp; omega))
    simpa using hp
  | succ count ih =>
    have hi := ih (pre ++ [false])
    have htail : Prefix machine (pre.length + (count + 1) + 1 + tail.length) (count + 1)
        (config 0 (pre ++ false :: (List.replicate count true ++ false :: tail)) (pre.length + 1))
        (config 1 (pre ++ List.replicate (count + 1) false ++ true :: tail) (pre.length + (count + 1))) := by
      simpa [List.replicate_succ, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
    have hs := carry_step pre (List.replicate count true ++ false :: tail)
    have hp := Prefix.step (by simp; omega :
        (config 0 (pre ++ true :: (List.replicate count true ++ false :: tail)) pre.length).tapeCells ≤
        pre.length + (count + 1) + 1 + tail.length)
      (by rfl : machine.halted (0 : Fin 2) = false) hs htail
    simpa [List.replicate_succ, List.append_assoc] using hp

theorem carry_run (count : ℕ) (tail : List Bool) :
    ∃ r : ExecutionReceipt 1 2,
      run machine (count + 1) (fun _ => List.replicate count true ++ false :: tail) = some r ∧
      r.final = config 1 (List.replicate count false ++ true :: tail) count ∧
      r.steps = count + 1 ∧ r.peakTapeCells ≤ count + 1 + tail.length := by
  have hp := carry_prefix count [] tail
  obtain ⟨r, hr, hf, hs, hb⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, by simpa [run, initialConfiguration, machine, config] using hr,
    by simpa using hf, hs, by simpa using hb⟩

theorem increment_value (count : ℕ) (tail : List Bool) :
    value (List.replicate count false ++ true :: tail) =
      value (List.replicate count true ++ false :: tail) + 1 := by
  induction count with
  | zero => simp [value, Nat.add_comm]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, value, Bool.toNat_false, Bool.toNat_true]
    omega

theorem workspace_run (count capacity : ℕ) (tail : List Bool)
    (hc : capacity ≤ count + 1 + tail.length) :
    ∃ r : ExecutionReceipt 2 4,
      run (Rewind.machine machine) (2 * count + 4)
        (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
          (fun _ : Fin 1 => List.replicate count true ++ false :: tail)
          (fun _ : Fin 1 => List.replicate capacity false)) = some r ∧
      r.final.tapes 0 = List.replicate count false ++ true :: tail ∧
      r.final.tapes 1 = List.replicate (max capacity (count + 1)) false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 2 * count + 4 ∧
      r.peakTapeCells ≤ 3 * (count + 1 + tail.length) := by
  obtain ⟨raw, hr, hf, hs, hp⟩ := carry_run count tail
  obtain ⟨r, hrun, ht, hcounter, hh, hsteps, hpeak⟩ :=
    Rewind.Workspace.reset_workspace machine (count + 1)
      (fun _ => List.replicate count true ++ false :: tail) raw hr capacity
  refine ⟨r, ?_, ?_, ?_, hh, ?_, ?_⟩
  · simpa [hs, Nat.mul_add, Nat.add_assoc] using hrun
  · simpa [hf, config] using ht (0 : Fin 1)
  · simpa [hs] using hcounter
  · omega
  · omega

end NearCubicWires.RepairOrdinary.BinaryIncrement

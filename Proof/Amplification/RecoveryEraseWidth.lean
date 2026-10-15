import Proof.Amplification.RecoveryFieldCopy

/-! Produce a nonempty width sentinel from a framed word. The single extra
mark makes the later polynomial erase driver cover the empty input as well. -/
namespace NearCubicWires.RepairOrdinary.RecoveryEraseWidth
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 3) (move : HeadMove) (write : Option Bool := none) : Action 1 3 :=
  ⟨q, fun _ => write, fun _ => move⟩
def incrementMachine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then action 0 .right else action 1 .left (some true))
    else if q.val = 1 then some (if bits 0 then action 1 .left else action 2 .right)
    else none

def cfg (q : Fin 3) (count pos : Nat) : Configuration 1 3 :=
  ⟨q, fun _ => pos, fun _ => CompareMachine.word count⟩

theorem scan_step (count pos : Nat) (hp : pos < count) :
    step incrementMachine (cfg 0 count (pos+1)) = some (cfg 0 count (pos+2)) := by
  simp [step, incrementMachine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem append_step (count : Nat) :
    step incrementMachine (cfg 0 count (count+1)) = some (cfg 1 (count+1) count) := by
  simp [step, incrementMachine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · funext i
    simp only [applyAction, action]
    have h := Streaming.write_append (CompareMachine.word count) true
    simpa [CompareMachine.word, List.replicate_add] using h

theorem rewind_step (count pos : Nat) (hp : pos < count) :
    step incrementMachine (cfg 1 count (pos+1)) = some (cfg 1 count pos) := by
  simp [step, incrementMachine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem stop_step (count : Nat) :
    step incrementMachine (cfg 1 count 0) = some (cfg 2 count 1) := by
  simp [step, incrementMachine, cfg, Configuration.scanned]
  rfl

theorem scan_prefix (remaining count pos : Nat) (hp : pos+remaining ≤ count) :
    Timed incrementMachine remaining (cfg 0 count (pos+1)) (cfg 0 count (pos+remaining+1)) := by
  induction remaining generalizing pos with
  | zero => simpa using Timed.refl incrementMachine (cfg 0 count (pos+1))
  | succ remaining ih =>
    have h := Timed.step (by rfl) (scan_step count pos (by omega)) (ih (pos+1) (by omega))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem rewind_prefix (count pos : Nat) (hp : pos ≤ count) :
    Timed incrementMachine (pos+1) (cfg 1 count pos) (cfg 2 count 1) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (stop_step count)
  | succ pos ih => exact Timed.step (by rfl) (rewind_step count pos (by omega)) (ih (by omega))

theorem increment_run (count : Nat) :
    ∃ r : ExecutionReceipt 1 3,
      runFrom incrementMachine (2*count+2) (cfg 0 count 1) = some r ∧
      r.final = cfg 2 (count+1) 1 ∧ r.steps = 2*count+2 := by
  have hscan := scan_prefix count count 0 (by omega)
  simp only [Nat.zero_add] at hscan
  have htail := Timed.step (by rfl) (append_step count) (rewind_prefix (count+1) count (by omega))
  have h := hscan.trans htail
  have he : count+(count+1+1)=2*count+2 := by omega
  rw [he] at h
  exact h.run (by rfl)

def slot : Fin 1 → Fin 2 := fun _ => 1
theorem slot_injective : Function.Injective slot := by decide
noncomputable def focusedIncrement := RecoveryFocus.machine slot incrementMachine
noncomputable def rawMachine := Composition.machine LengthMachine.machine focusedIncrement
noncomputable def machine := Rewind.machine rawMachine

theorem raw_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 2 9,
      run rawMachine (6*bits.length+6) ![frame bits,[]] = some r ∧
      r.final.tapes = ![frame bits,CompareMachine.word (bits.length+1)] ∧ r.steps = 6*bits.length+6 := by
  obtain ⟨first, hfirst, hf, hs, _⟩ := LengthMachine.length_run bits
  obtain ⟨base, hbase, hbf, hbs⟩ := increment_run bits.length
  obtain ⟨second, hsecond, hsf, hss⟩ := RecoveryFocus.run_config slot slot_injective incrementMachine
    ![0,1] ![frame bits,CompareMachine.word bits.length] (2*bits.length+2) _ base hbase
  have hin : RecoveryFocus.config slot ![0,1] ![frame bits,CompareMachine.word bits.length] (cfg 0 bits.length 1) =
      Composition.restart first.final focusedIncrement.start := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [RecoveryFocus.config, 
        slot, Composition.restart, cfg, LengthMachine.cfg, RecoveryFocus.pick]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config, 
        slot, Composition.restart, cfg, LengthMachine.cfg, RecoveryFocus.pick, CompareMachine.word]
  rw [hin] at hsecond
  have h := Composition.run_join LengthMachine.machine focusedIncrement (4*bits.length+3)
    (2*bits.length+2) _ first second hfirst hsecond
  have he : 4*bits.length+3+1+(2*bits.length+2)=6*bits.length+6 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt first second,h,?_,?_⟩
  · rw [Composition.joinedReceipt,hsf,hbf]
    funext i
    fin_cases i <;> simp [Composition.rightConfig, RecoveryFocus.config, cfg,
       slot, RecoveryFocus.pick]
  · simp only [Composition.joinedReceipt, hs, hss, hbs]
    omega

theorem width_ready (bits : List Bool) (capacity : Nat) :
    ReadyRun machine (12*bits.length+14)
      ![frame bits,[],List.replicate capacity false]
      ![frame bits,CompareMachine.word (bits.length+1),
        List.replicate (max capacity (6*bits.length+6)) false] := by
  obtain ⟨source,hr,ht,hs⟩ := raw_run bits
  obtain ⟨r,hrun,hbase,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace rawMachine _ _ source hr capacity
  have he : 2*source.steps+2=12*bits.length+14 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [ht] using hbase 0
    · simpa [ht] using hbase 1
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryEraseWidth

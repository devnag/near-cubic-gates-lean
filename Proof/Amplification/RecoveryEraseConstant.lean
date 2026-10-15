import Proof.Amplification.RecoveryEraseWidth

/-! A fixed finite controller writes the literal coefficient used by the
polynomial scratch erase driver. Its writes and head rewind are charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryEraseConstant
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine (count : Nat) : Machine 1 (count+1) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == count
  rule := fun q _ => if h : q.val < count then
    some ⟨⟨q.val+1,by omega⟩,fun _ => some true,fun _ => .right⟩ else none

def cfg (count pos : Nat) (hp : pos ≤ count) : Configuration 1 (count+1) :=
  ⟨⟨pos,by omega⟩,fun _ => pos,fun _ => List.replicate pos true⟩

theorem write_step (count pos : Nat) (hp : pos < count) :
    step (machine count) (cfg count pos (by omega)) = some (cfg count (pos+1) (by omega)) := by
  simp [step,machine,cfg,hp]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    simp only [applyAction]
    have h := Streaming.write_append (List.replicate pos true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using h

theorem write_prefix (count remaining pos : Nat) (hp : pos+remaining=count) :
    Timed (machine count) remaining (cfg count pos (by omega)) (cfg count count (Nat.le_refl _)) := by
  induction remaining generalizing pos with
  | zero =>
    have he : pos=count := by omega
    subst pos
    exact Timed.refl _ _
  | succ remaining ih =>
    exact Timed.step (by simp [machine,cfg]; omega) (write_step count pos (by omega))
      (ih (pos+1) (by omega))

theorem constant_run (count : Nat) :
    ∃ r : ExecutionReceipt 1 (count+1),
      run (machine count) count (fun _ => []) = some r ∧
      r.final.tapes = (fun _ => List.replicate count true) ∧ r.steps=count := by
  obtain ⟨r,hr,hf,hs⟩ := (write_prefix count count 0 (by omega)).run (by simp [machine,cfg])
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

def resetMachine (count : Nat) : Machine 2 (count+1+2) := Rewind.machine (machine count)

theorem constant_ready (count : Nat) :
    ReadyRun (resetMachine count) (2*count+2) (fun _ => [])
      ![List.replicate count true,List.replicate count false] := by
  obtain ⟨source,hr,ht,hs⟩ := constant_run count
  obtain ⟨r,hrun,hbase,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace (machine count) _ _ source hr 0
  have he : 2*source.steps+2=2*count+2 := by rw [hs]
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [ht] using hbase 0
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryEraseConstant

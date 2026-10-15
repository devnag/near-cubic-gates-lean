import Proof.Amplification.RecoveryCertificateTableFirst

/-! A bounded physical copy for retaining the shared valuation copied.
The unary driver is retained and every copied source cell is charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTapeCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copied (source : List Bool) (count : Nat) : List Bool :=
  (List.range count).map (readTapeBit source)
@[simp] theorem prefix_length (source : List Bool) (count : Nat) :
    (copied source count).length=count := by simp [copied]
theorem prefix_succ (source : List Bool) (count : Nat) :
    copied source (count+1)=copied source count++[readTapeBit source count] := by
  simp [copied,List.range_succ,List.map_append]

def raw : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then
    if bits 2 then some ⟨0,![none,some (bits 0),none],fun _=>.right⟩
    else some ⟨1,fun _=>none,fun _=>.stay⟩
    else none

def cfg (q : Fin 2) (source : List Bool) (total done : Nat) : Configuration 3 2 :=
  ⟨q,fun _=>done,![source,copied source done,List.replicate total true]⟩

theorem copy_step (source : List Bool) (total done : Nat) (hd : done<total) :
    step raw (cfg 0 source total done)=some (cfg 0 source total (done+1)) := by
  have hread : readTapeBit (List.replicate total true) done=true := by simp [readTapeBit,List.getD,hd]
  simp [step,raw,cfg,Configuration.scanned,hread]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,prefix_succ]
    simpa using Streaming.write_append (copied source done) (readTapeBit source done)

theorem stop_step (source : List Bool) (total : Nat) :
    step raw (cfg 0 source total total)=some (cfg 1 source total total) := by
  have hread : readTapeBit (List.replicate total true) total=false := by simp [readTapeBit,List.getD]
  simp [step,raw,cfg,Configuration.scanned,hread]
  rfl

theorem copy_prefix (remaining done : Nat) (source : List Bool) :
    Timed raw (remaining+1) (cfg 0 source (done+remaining) done)
      (cfg 1 source (done+remaining) (done+remaining)) := by
  induction remaining generalizing done with
  | zero => simpa using Timed.single (by rfl) (stop_step source done)
  | succ remaining ih =>
    have h := ih (done+1)
    have he : done+1+remaining=done+(remaining+1) := by omega
    rw [he] at h
    exact Timed.step (by rfl) (copy_step source (done+(remaining+1)) done (by omega)) h

def machine := Rewind.machine raw

theorem copy_ready (source : List Bool) (total capacity : Nat) :
    ReadyRun machine (2*total+4)
      ![source,[],List.replicate total true,List.replicate capacity false]
      ![source,copied source total,List.replicate total true,List.replicate (max capacity (total+1)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := (copy_prefix total 0 source).run (by rfl)
  have hi : cfg 0 source (0+total) 0=initialConfiguration raw ![source,[],List.replicate total true] := by
    simp only [Nat.zero_add]
    rfl
  rw [hi] at hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr capacity
  have he : 2*base.steps+2=2*total+4 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf,cfg] using ht 0
    · simpa [hf,cfg] using ht 1
    · simpa [hf,cfg] using ht 2
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryBoundedTapeCopy

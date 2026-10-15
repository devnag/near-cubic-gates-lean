import Proof.Amplification.RecoveryBoundedTapeCopy

/-! Close a bounded physical copy before rewinding it. The copied prefix
therefore has an actual false delimiter; the unread witness suffix is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedWordCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def close : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,![none,some false,none],fun _=>.stay⟩ else none

def closeCfg (q : Fin 2) (source : List Bool) (total : Nat) (out : List Bool) : Configuration 3 2 :=
  ⟨q,fun _=>total,![source,out,List.replicate total true]⟩

theorem close_run (source : List Bool) (total : Nat) :
    ∃ r,runFrom close 1 (closeCfg 0 source total (copied source total))=some r ∧
      r.final=closeCfg 1 source total (copied source total++[false]) ∧ r.steps=1 := by
  have h : step close (closeCfg 0 source total (copied source total))=
      some (closeCfg 1 source total (copied source total++[false])) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,closeCfg]
      simpa using Streaming.write_append (copied source total) false
  exact (Timed.single (by rfl) h).run (by rfl)

def raw := Composition.machine RecoveryBoundedTapeCopy.raw close
def machine := Rewind.machine raw

theorem raw_run (source : List Bool) (total : Nat) :
    ∃ r,run raw (total+3) ![source,[],List.replicate total true]=some r ∧
      r.final.tapes=![source,copied source total++[false],List.replicate total true] ∧ r.steps=total+3 := by
  obtain ⟨first,hfirst,hf,hs⟩ := (copy_prefix total 0 source).run (by rfl)
  obtain ⟨last,hlast,ht,hn⟩ := close_run source total
  have hi : Composition.restart first.final close.start=closeCfg 0 source total (copied source total) := by
    rw [hf]
    simp [Composition.restart,cfg,closeCfg,close]
  rw [← hi] at hlast
  have h := Composition.run_join RecoveryBoundedTapeCopy.raw close (total+1) 1 _ first last hfirst hlast
  have he : total+1+1+1=total+3 := by omega
  rw [he] at h
  have hinput : Composition.leftConfig 2 (cfg 0 source (0+total) 0)=
      initialConfiguration raw ![source,[],List.replicate total true] := by
    simp only [Nat.zero_add]
    rfl
  rw [hinput] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,?_⟩
  · simp only [Composition.joinedReceipt,Composition.rightConfig,ht,closeCfg]
  · simp only [Composition.joinedReceipt,hs,hn]

theorem copy_ready (source : List Bool) (total capacity : Nat) :
    ReadyRun machine (2*total+8)
      ![source,[],List.replicate total true,List.replicate capacity false]
      ![source,copied source total++[false],List.replicate total true,
        List.replicate (max capacity (total+3)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := raw_run source total
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr capacity
  have he : 2*base.steps+2=2*total+8 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf] using ht 0
    · simpa [hf] using ht 1
    · simpa [hf] using ht 2
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryBoundedWordCopy

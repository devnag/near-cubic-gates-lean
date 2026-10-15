import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.MachineModel.Runs

/-! The existing bounded raw copier overwrites arbitrary bounded backing.
This receipt removes a separate erase pass when replacing a Pascal row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Overwrite
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryBoundedTapeCopy
open StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (state : Fin 2) (source backing : List Bool) (total done : ℕ):Configuration 3 2:=
  ⟨state,fun _=>done,![source,overlay (copied source done) backing,List.replicate total true]⟩

theorem copy_step (source backing : List Bool) (total done : ℕ) (hd:done<total):
    step raw (cfg 0 source backing total done)=some (cfg 0 source backing total (done+1)):=by
  have hread:readTapeBit (List.replicate total true) done=true:=by simp [readTapeBit,List.getD,hd]
  simp [step,raw,cfg,Configuration.scanned,hread]
  apply configuration_ext
  · rfl
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,prefix_succ]
    simpa only [prefix_length] using overlay_write (copied source done) backing (readTapeBit source done)

theorem stop_step (source backing : List Bool) (total : ℕ):
    step raw (cfg 0 source backing total total)=some (cfg 1 source backing total total):=by
  have hread:readTapeBit (List.replicate total true) total=false:=by simp [readTapeBit,List.getD]
  simp [step,raw,cfg,Configuration.scanned,hread]
  rfl

theorem copy_prefix (remaining done : ℕ) (source backing : List Bool):
    Timed raw (remaining+1) (cfg 0 source backing (done+remaining) done)
      (cfg 1 source backing (done+remaining) (done+remaining)):=by
  induction remaining generalizing done with
  | zero=>simpa using Timed.single (by rfl) (stop_step source backing done)
  | succ remaining ih=>
    have h:=ih (done+1)
    have he:done+1+remaining=done+(remaining+1):=by omega
    rw [he] at h
    exact Timed.step (by rfl) (copy_step source backing (done+(remaining+1)) done (by omega)) h

theorem ready (source backing : List Bool) (D C : ℕ)
    (hs:source.length=D) (hb:backing.length≤D) (hC:D+1≤C):
    ReadyRun RecoveryBoundedTapeCopy.machine (2*D+4)
      ![source,backing,List.replicate D true,List.replicate C false]
      ![source,source,List.replicate D true,List.replicate C false]:=by
  obtain ⟨base,hr,hf,ht⟩:=(copy_prefix D 0 source backing).run (by rfl)
  have hi:cfg 0 source backing (0+D) 0=
      initialConfiguration raw ![source,backing,List.replicate D true]:=by
    apply configuration_ext
    · rfl
    · rfl
    · simp [cfg,initialConfiguration,copied,overlay]
  rw [hi] at hr
  obtain ⟨r,run,rt,log,rh,rs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ base hr C
  have time:2*base.steps+2=2*D+4:=by rw [ht];omega
  rw [time] at run
  have cp:copied source D=source:=by rw [←hs];exact CloseoutRowsMetadataCopy.copied_self source
  have ov:overlay (copied source D) backing=source:=by
    rw [cp,overlay,List.drop_eq_nil_of_le (by omega : backing.length ≤ source.length),List.append_nil]
  refine ⟨r,?_,?_,rh,rs.trans time⟩
  · convert run using 2
    all_goals first | rfl | (funext i;fin_cases i <;> rfl)
  · funext i;fin_cases i
    · simpa [hf,cfg] using rt 0
    · simpa [hf,cfg,ov] using rt 1
    · simpa [hf,cfg] using rt 2
    · simpa [ht,Nat.max_eq_left hC] using log

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Overwrite

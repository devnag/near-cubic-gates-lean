import Proof.Amplification.RecoveryPaddedCopy

/-! The complete fixed-width padded copy, including actual driver
positioning and reset of all four heads. Output framing and zero padding
are physically written, and the original source is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdPaddedCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loop_trace (bits : List Bool) (width k remaining : Nat) (hk : k+remaining=width) :
    Timed loop (2*remaining+1) (cfg bits width k) (final bits width) := by
  induction remaining generalizing k with
  | zero=>
    have he : k=width := by omega
    subst k
    exact Timed.single (by rfl) (stop_step bits width)
  | succ remaining ih=>
    have h := ((Timed.single (by rfl) (marker_step bits width k (by omega))).trans
      (Timed.single (by rfl) (data_step bits width k))).trans (ih (k+1) (by omega))
    have he : 1+1+(2*remaining+1)=2*(remaining+1)+1 := by omega
    rw [he] at h
    exact h

def raw := Composition.machine RecoveryFieldCopy.positionMachine loop
def machine := Rewind.machine raw

theorem raw_run (bits : List Bool) (width : Nat) :
    ∃ r,run raw (2*width+3) ![frame bits,[],CompareMachine.word width]=some r ∧
      r.final.tapes=![frame bits,frame (data bits width),CompareMachine.word width] ∧ r.steps=2*width+3 := by
  have hstep : step RecoveryFieldCopy.positionMachine
      (initialConfiguration RecoveryFieldCopy.positionMachine ![frame bits,[],CompareMachine.word width])=
      some (⟨1,![0,0,1],![frame bits,[],CompareMachine.word width]⟩ : Configuration 3 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨first,hfirst,hf,hs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨last,hlast,hl,ht⟩ := (loop_trace bits width 0 width (by omega)).run (by rfl)
  have hi : Composition.restart first.final loop.start=cfg bits width 0 := by rw [hf]; rfl
  rw [←hi] at hlast
  have h := Composition.run_join RecoveryFieldCopy.positionMachine loop 1 (2*width+1) _ first last hfirst hlast
  rw [show 1+1+(2*width+1)=2*width+3 by omega] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,?_⟩
  · simp only [Composition.joinedReceipt,Composition.rightConfig,hl,final]
  · simp only [Composition.joinedReceipt,hs,ht]
    omega

theorem copy_ready (bits : List Bool) (width : Nat) :
    ReadyRun machine (4*width+8) ![frame bits,[],CompareMachine.word width,[]]
      ![frame bits,frame (data bits width),CompareMachine.word width,List.replicate (2*width+3) false] := by
  obtain ⟨base,hbase,hbt,hsteps⟩ := raw_run bits width
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw (2*width+3)
    ![frame bits,[],CompareMachine.word width] base hbase 0
  have he : 2*base.steps+2=4*width+8 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hs.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hbt] using ht 0
    · simpa [hbt] using ht 1
    · simpa [hbt] using ht 2
    · simpa [hsteps] using hcounter

end NearCubicWires.RepairOrdinary.RecoveryColdPaddedCopy

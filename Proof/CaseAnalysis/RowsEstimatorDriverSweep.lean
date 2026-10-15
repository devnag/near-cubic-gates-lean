import Proof.CaseAnalysis.RowsEstimatorDriverSupport
import Proof.Hierarchy.CompetitorRecordRewind

/-! Existing ordinary sweep and return workers at offset cursors.
A fixed sequence of D passes can clear K*D cells without producing K*D. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
open LocalBitMultitape RecoveryExecution RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {t : ℕ} (q : Fin 2) (D offset done : ℕ) (backing : Fin t → List Bool) : Configuration (t+1) 2 :=
  ⟨q,Fin.addCases (fun _ : Fin t => offset+done) (fun _ : Fin 1 => done),
    RecoveryScratchErase.tapes D (offset+done) backing⟩

theorem next {t : ℕ} (D offset done : ℕ) (backing : Fin t → List Bool) (hd : done<D) :
    step (RecoveryScratchErase.machine t) (cfg 0 D offset done backing)=
      some (cfg 0 D offset (done+1) backing) := by
  have hread : readTapeBit (List.replicate D true) done=true := by simp [readTapeBit,List.getD,hd]
  simp only [step,RecoveryScratchErase.machine,cfg,Configuration.scanned,RecoveryScratchErase.tapes,
    Fin.addCases_right,hread,Fin.val_zero,ite_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j => ?_) (fun j => ?_) i <;>
      simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j => ?_) (fun j => ?_) i
    · simp only [applyAction,RecoveryScratchErase.tapes,Fin.addCases_left]
      have h := overlay_write (List.replicate (offset+done) false) (backing j) false
      have he : List.replicate (offset+(done+1)) false=List.replicate (offset+done) false++[false] := by
        rw [show offset+(done+1)=(offset+done)+1 by omega,List.replicate_add]
        rfl
      rw [he]
      simpa only [List.length_replicate] using h
    · simp only [applyAction,RecoveryScratchErase.tapes,Fin.addCases_right]

theorem stop {t : ℕ} (D offset : ℕ) (backing : Fin t → List Bool) :
    step (RecoveryScratchErase.machine t) (cfg 0 D offset D backing)=
      some (cfg 1 D offset D backing) := by
  have hread : readTapeBit (List.replicate D true) D=false := by simp [readTapeBit,List.getD]
  simp only [step,RecoveryScratchErase.machine,cfg,Configuration.scanned,RecoveryScratchErase.tapes,
    Fin.addCases_right,hread,Fin.val_zero,ite_true,Bool.false_eq_true,ite_false]
  rfl

theorem forward {t : ℕ} (D offset : ℕ) (backing : Fin t → List Bool) : ∃ r,
    runFrom (RecoveryScratchErase.machine t) (D+1) (cfg 0 D offset 0 backing)=some r ∧
      r.final=cfg 1 D offset D backing ∧ r.steps=D+1 := by
  have loop (remaining done : ℕ) (he : done+remaining=D) :
      Timed (RecoveryScratchErase.machine t) (remaining+1) (cfg 0 D offset done backing)
        (cfg 1 D offset D backing) := by
    induction remaining generalizing done with
    | zero =>
      have hd : done=D := by omega
      subst done
      exact Timed.single (by rfl) (stop D offset backing)
    | succ remaining ih =>
      exact Timed.step (by rfl) (next D offset done backing (by omega)) (ih (done+1) (by omega))
  exact (loop D 0 (by omega)).run (by rfl)

theorem return_partial (source : List Bool) (D pos : ℕ) : ∃ r,
    runFrom CompetitorRecordRewind.machine (2*D+2)
      (CompetitorRecordRewind.cfg 0 source pos D 0 0 [])=some r ∧
      r.final=CompetitorRecordRewind.cfg 2 source (pos-D) D 0 0 (List.replicate D false) ∧
      r.steps=2*D+2 := by
  have hf := CompetitorRecordRewind.forward_timed source pos D D 0 (by omega)
  have hb := CompetitorRecordRewind.back_timed source (pos-D) D D 0
  simp only [Nat.sub_zero,Nat.add_zero,List.replicate_zero,List.append_nil] at hf hb
  have h := hf.trans hb
  have he : D+1+(D+1)=2*D+2 := by omega
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep

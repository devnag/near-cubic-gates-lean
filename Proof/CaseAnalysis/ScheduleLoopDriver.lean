import Proof.CaseAnalysis.ScheduleStep
import Proof.PCP.VerifierDecodingRepeat

/-! Use the existing literal repeat controller only at the input's actual
bounded indices. No artificial post-exhaustion body invariant is required. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.LoopDriver
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem run {t states : Nat} (body : Machine t states) (input : Nat→Fin t→List Bool)
    (total cost : Nat)
    (supplier : ∀ j,j < total → ClockJoin.ReadyRun body cost (input j) (input (j+1)))
    (remaining done : Nat) (hsum : done+remaining=total) : ∃ r,
    runFrom (RepeatMachine.machine body (fun _ _=>true)) (remaining*(cost+2)+total+3)
      (RepeatMachine.cfg 0 (initialConfiguration body (input done)) total (done+1))=some r ∧
    r.steps ≤ remaining*(cost+2)+total+3 ∧
    r.final=RepeatMachine.cfg 3 (initialConfiguration body (input total)) total 1 := by
  induction remaining generalizing done with
  | zero=>
    have hd : done=total := by omega
    subst done
    obtain ⟨r,hr,hf,hs⟩:=(RepeatMachine.exhaust body (fun _ _=>true)
      (initialConfiguration body (input total)) total).run (by
        simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa using hr,by simpa using hs.le,hf⟩
  | succ remaining ih=>
    obtain ⟨a,ha,atapes,aheads,asteps⟩:=supplier done (by omega)
    have hp:=RepeatMachine.iteration body (fun _ _=>true)
      (initialConfiguration body (input done)) total done a rfl (by omega) ha
    simp only [↓reduceIte] at hp
    have he : RepeatMachine.cfg 0 a.final total (done+2)=
        RepeatMachine.cfg 0 (initialConfiguration body (input (done+1))) total ((done+1)+1) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,funext aheads,initialConfiguration,Nat.add_assoc]
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,atapes,initialConfiguration]
    rw [he] at hp
    obtain ⟨tail,htail,hsteps,hfinal⟩:=ih (done+1) (by omega)
    obtain ⟨space,path⟩:=hp
    obtain ⟨r,hr,hf,hs,_⟩:=path.followedBy tail htail
    have hbudget : (a.steps+2)+(remaining*(cost+2)+total+3) ≤ (remaining+1)*(cost+2)+total+3 := by
      nlinarith
    have hmore:=runFrom_moreFuel (RepeatMachine.machine body (fun _ _=>true)) _
      ((remaining+1)*(cost+2)+total+3-((a.steps+2)+(remaining*(cost+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le hbudget] at hmore
    refine ⟨r,hmore,?_,hf.trans hfinal⟩
    rw [hs]
    nlinarith

end
end NearCubicWires.RepairSource.CloseoutSchedule.LoopDriver

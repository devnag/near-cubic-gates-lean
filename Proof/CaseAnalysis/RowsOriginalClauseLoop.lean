import Proof.CaseAnalysis.RowsTupleSeekRepeat
import Proof.CaseAnalysis.RowsOriginalFixedLoop

/-! The physical original clause-count driver controls each complete
clause action. No action is requested at the exhausted index N. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClauseLoop
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem trace {t s : ℕ} (p : Machine t s) (N cost : ℕ)
    (H : ℕ→Fin t→ℕ) (A : ℕ→Fin t→List Bool)
    (supplier : ∀ j<N,Step p cost (H j) (A j) (H (j+1)) (A (j+1)))
    (remaining done : ℕ) (hcount : done+remaining=N) :
    ∃ time≤remaining*(cost+2)+N+3,Timed (RepeatMachine.machine p (fun _ _=>true)) time
      (RepeatMachine.cfg 0 (⟨p.start,H done,A done⟩ : Configuration t s) N (done+1))
      (RepeatMachine.cfg 3 (⟨p.start,H N,A N⟩ : Configuration t s) N 1) := by
  induction remaining generalizing done with
  | zero=>
    have hd : done=N:=by omega
    subst done
    exact ⟨N+3,by simp,RepeatMachine.exhaust p (fun _ _=>true) _ N⟩
  | succ remaining ih=>
    obtain ⟨r,hr,rh,rt,rs⟩:=supplier done (by omega)
    have first:=RepeatMachine.iteration p (fun _ _=>true)
      (⟨p.start,H done,A done⟩ : Configuration t s) N done r rfl (by omega) hr
    simp only [↓reduceIte] at first
    rw [RowOccurrenceLoop.cfg_eq 0 r.final (⟨p.start,H (done+1),A (done+1)⟩ : Configuration t s)
      N (done+2) rh rt] at first
    obtain ⟨time,ht,tail⟩:=ih (done+1) (by omega)
    have both:=first.trans tail
    refine ⟨r.steps+2+time,?_,both⟩
    simp only [Nat.succ_mul]
    omega

theorem run {t s : ℕ} (p : Machine t s) (N cost : ℕ)
    (H : ℕ→Fin t→ℕ) (A : ℕ→Fin t→List Bool)
    (supplier : ∀ j<N,Step p cost (H j) (A j) (H (j+1)) (A (j+1))) :
    Step (RepeatMachine.machine p (fun _ _=>true)) (N*(cost+3)+3)
      (Fin.addCases (H 0) (fun _ : Fin 1=>1))
      (Fin.addCases (A 0) (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases (H N) (fun _ : Fin 1=>1))
      (Fin.addCases (A N) (fun _ : Fin 1=>CompareMachine.word N)) := by
  obtain ⟨time,ht,tr⟩:=trace p N cost H A supplier N 0 (by omega)
  have bound : time≤N*(cost+3)+3:=by nlinarith
  obtain ⟨r,hr,hf,_⟩:=tr.run (by simp [RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])
  exact (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).enlarge bound

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClauseLoop

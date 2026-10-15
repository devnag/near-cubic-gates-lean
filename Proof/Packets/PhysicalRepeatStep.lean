import Proof.PCP.VerifierDecodingRepeatBody
import Proof.MachineModel.Runs

/-! A bounded actual repeat adapter. Body executions are required only at
indices strictly below the physical driver count; no terminal body call is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace FixedLivePackets.Materializer.PhysicalRepeatStep
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def cfg {t s : Nat} (body : Machine t s) (H : Nat→Fin t→Nat)
    (A : Nat→Fin t→List Bool) (phase : Fin 5) (i total pos : Nat) :=
  RepeatMachine.cfg phase (⟨body.start,H i,A i⟩) total pos

theorem remaining {t s : Nat} (body : Machine t s) (N E : Nat)
    (H : Nat→Fin t→Nat) (A : Nat→Fin t→List Bool)
    (hbody : ∀ i, i<N→Step body E (H i) (A i) (H (i+1)) (A (i+1)))
    (n pos : Nat) (hn : pos+n=N) :
    ∃ r,runFrom (RepeatMachine.machine body (fun _ _=>true)) (n*(E+2)+N+3)
      (cfg body H A 0 pos N (pos+1))=some r ∧
      r.final=cfg body H A 3 N N 1 ∧ r.steps≤n*(E+2)+N+3 := by
  induction n generalizing pos with
  | zero =>
    have hp : pos=N := by omega
    subst pos
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust body (fun _ _=>true)
      (⟨body.start,H N,A N⟩) N).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,rf,?_⟩
    · simpa [cfg] using rr
    · simpa using rs.le
  | succ n ih =>
    obtain ⟨r,rr,rh,rt,rs⟩:=hbody pos (by omega)
    have first:=RepeatMachine.iteration body (fun _ _=>true)
      (⟨body.start,H pos,A pos⟩) N pos r rfl (by omega) rr
    simp only [ite_true] at first
    have exit : RepeatMachine.cfg 0 r.final N (pos+2)=cfg body H A 0 (pos+1) N (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,rh]
      · simp [cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,rt]
    rw [exit] at first
    obtain ⟨last,lr,lf,ls⟩:=ih (pos+1) (by omega)
    have lr' : runFrom (RepeatMachine.machine body (fun _ _=>true)) (n*(E+2)+N+3)
        (cfg body H A 0 (pos+1) N (pos+2))=some last := by
      simpa only [Nat.add_assoc] using lr
    rcases first with ⟨space,hfirst⟩
    obtain ⟨result,resultRun,resultFinal,resultSteps,_⟩:=hfirst.followedBy last lr'
    have fit : (r.steps+2)+(n*(E+2)+N+3)≤(n+1)*(E+2)+N+3 := by nlinarith
    have more:=runFrom_moreFuel (RepeatMachine.machine body (fun _ _=>true)) _
      ((n+1)*(E+2)+N+3-((r.steps+2)+(n*(E+2)+N+3))) _ result resultRun
    rw [Nat.add_sub_of_le fit] at more
    exact ⟨result,more,resultFinal.trans lf,by rw [resultSteps];nlinarith⟩

/-- A fixed repeat machine executes exactly the first `N` supplied local
steps and restores its own physical unary count driver. -/
theorem run {t s : Nat} (body : Machine t s) (N E : Nat)
    (H : Nat→Fin t→Nat) (A : Nat→Fin t→List Bool)
    (hbody : ∀ i, i<N→Step body E (H i) (A i) (H (i+1)) (A (i+1))) :
    Step (RepeatMachine.machine body (fun _ _=>true)) (N*(E+3)+3)
      (Fin.addCases (H 0) (fun _ : Fin 1=>1))
      (Fin.addCases (A 0) (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases (H N) (fun _ : Fin 1=>1))
      (Fin.addCases (A N) (fun _ : Fin 1=>CompareMachine.word N)) := by
  obtain ⟨r,rr,rf,_⟩:=remaining body N E H A hbody N 0 (by omega)
  have fuel : N*(E+2)+N+3=N*(E+3)+3 := by ring
  rw [fuel] at rr
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end
end FixedLivePackets.Materializer.PhysicalRepeatStep

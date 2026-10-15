import Proof.CaseAnalysis.RecoveryTableIndexStep

/-! The existing sentinel driver repeats the paid three-index step. Two
calls with the actual field limit and one with the retained six driver give
the original row width without introducing another input field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexLoop
open LocalBitMultitape RepairRepresentation
open RepairSource.VerifierDecoding RecoveryBoundedTableIndexStep
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 4→Bool):=true
noncomputable def machine:=RepeatMachine.machine RecoveryBoundedTableIndexStep.machine accepted
noncomputable def base (a b c C : ℕ):=initialConfiguration RecoveryBoundedTableIndexStep.machine (data ![a,b,c] C)
def budget (count W : ℕ):=count*(6*W+17)+3

theorem driver_run (remaining total pos a b c C W : ℕ) (hp : pos+remaining=total)
    (ha : a+remaining ≤ W) (hb : b+remaining ≤ W) (hc : c+remaining ≤ W) (hC : W+1 ≤ C) :
    ∃ r,runFrom machine (remaining*(6*W+16)+total+3)
      (RepeatMachine.cfg 0 (base a b c C) total (pos+1))=some r ∧
      r.steps ≤ remaining*(6*W+16)+total+3 ∧
      r.final=RepeatMachine.cfg 3 (base (a+remaining) (b+remaining) (c+remaining) C) total 1 := by
  induction remaining generalizing pos a b c with
  | zero =>
    have he : pos=total:=by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩:=(RepeatMachine.exhaust RecoveryBoundedTableIndexStep.machine accepted (base a b c C) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa only [Nat.zero_mul,Nat.zero_add,machine] using hr,
      by simpa only [Nat.zero_mul,Nat.zero_add] using hs.le,by simpa only [Nat.add_zero] using hf⟩
  | succ remaining ih =>
    obtain ⟨body,hr,ht,hh,hs⟩:=step_ready a b c C (by omega) (by omega) (by omega)
    have hr' : runFrom RecoveryBoundedTableIndexStep.machine (RecoveryBoundedTableIndexStep.budget a b c)
        (base a b c C)=some body:=hr
    have iteration:=RepeatMachine.iteration RecoveryBoundedTableIndexStep.machine accepted (base a b c C)
      total pos body rfl (by omega) hr'
    simp only [accepted,if_true] at iteration
    have hh' : body.final.heads=fun _=>0:=funext hh
    have he : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (base (a+1) (b+1) (c+1) C) total ((pos+1)+1) := by
      simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config]
      rw [hh',ht]
      rfl
    rw [he] at iteration
    obtain ⟨rest,rr,rs,rf⟩:=ih (pos+1) (a+1) (b+1) (c+1) (by omega) (by omega) (by omega) (by omega)
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,rrun,rfinal,rsteps,_⟩:=hprefix.followedBy rest rr
    have hbody : body.steps ≤ 6*W+14 := by
      rw [hs]
      unfold RecoveryBoundedTableIndexStep.budget
      omega
    have hbound : (body.steps+2)+(remaining*(6*W+16)+total+3) ≤
        (remaining+1)*(6*W+16)+total+3 := by nlinarith
    have more:=runFrom_moreFuel machine _
      (((remaining+1)*(6*W+16)+total+3)-((body.steps+2)+(remaining*(6*W+16)+total+3))) _ r rrun
    rw [Nat.add_sub_of_le hbound] at more
    refine ⟨r,more,?_,?_⟩
    · rw [rsteps]
      omega
    · rw [rfinal,rf]
      congr 2 <;> omega

theorem loop_run (a b c count C W : ℕ)
    (ha : a+count ≤ W) (hb : b+count ≤ W) (hc : c+count ≤ W) (hC : W+1 ≤ C) :
    ∃ r,runFrom machine (budget count W) (RepeatMachine.cfg 0 (base a b c C) count 1)=some r ∧
      r.steps ≤ budget count W ∧
      r.final=RepeatMachine.cfg 3 (base (a+count) (b+count) (c+count) C) count 1 := by
  obtain ⟨r,hr,hs,hf⟩:=driver_run count count 0 a b c C W (by omega) ha hb hc hC
  have he : count*(6*W+16)+count+3=budget count W := by unfold budget;ring
  rw [he] at hr hs
  exact ⟨r,hr,hs,hf⟩

theorem budget_quadratic (count W : ℕ) (hc : count ≤ W) :
    budget count W ≤ 32*(W+1)^2 := by
  have h:=Nat.mul_le_mul_right (6*W+17) hc
  unfold budget
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexLoop

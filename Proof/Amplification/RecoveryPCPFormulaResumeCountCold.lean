import Proof.Amplification.RecoveryPCPFormulaResumeCount
import Proof.MachineModel.UWalkUnary

/-! Produce the actual exponential randomness and tautology drivers from
the retained unary R field. The existing count machine and successor copy
both execute, including width zero, with paid head positioning and rewind. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCountCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def position : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=0 then .right else .stay⟩ else none
noncomputable def raw := Composition.machine position RecoveryPCPFormulaResumeCount.machine
noncomputable def readyMachine := Rewind.machine raw
def input (R : Nat) : Fin 7→List Bool :=
  Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool) (RecoveryPCPFormulaResumeCount.input R) (fun _=>[])
def budget (R : Nat) := 2*(RecoveryPCPFormulaResumeCount.budget R+2)+2

theorem raw_run (R : Nat) : ∃ r,
    run raw (RecoveryPCPFormulaResumeCount.budget R+2) (RecoveryPCPFormulaResumeCount.input R)=some r ∧
      r.final.tapes 0=CompareMachine.word R ∧ r.final.tapes 4=CompareMachine.word (2^R-1) ∧
      r.steps≤RecoveryPCPFormulaResumeCount.budget R+2 := by
  have hstep : step position (initialConfiguration position (RecoveryPCPFormulaResumeCount.input R))=
      some ⟨1,RecoveryPCPFormulaResumeCount.heads,RecoveryPCPFormulaResumeCount.input R⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨a,ha,af,as_⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨b,hb,_bh,b0,b4,bs⟩ := RecoveryPCPFormulaResumeCount.count_run R
  have he : Composition.restart a.final RecoveryPCPFormulaResumeCount.machine.start=
      (⟨RecoveryPCPFormulaResumeCount.machine.start,RecoveryPCPFormulaResumeCount.heads,
        RecoveryPCPFormulaResumeCount.input R⟩ : Configuration 6 _) := by rw [af]; rfl
  rw [←he] at hb
  have hall:=Composition.run_join position RecoveryPCPFormulaResumeCount.machine _ _ _ a b ha hb
  have ht : 1+1+RecoveryPCPFormulaResumeCount.budget R=RecoveryPCPFormulaResumeCount.budget R+2 := by omega
  rw [ht] at hall
  refine ⟨_,hall,b0,b4,?_⟩
  change a.steps+1+b.steps≤_
  omega

theorem count_ready (R : Nat) : ∃ out,
    ClockJoin.ReadyRun readyMachine (budget R) (input R) out ∧
      out 0=CompareMachine.word R ∧ out 4=CompareMachine.word (2^R-1) := by
  obtain ⟨base,hbase,b0,b4,bs⟩ := raw_run R
  obtain ⟨r,hr,rt,_rl,rh,rs,_rp⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase 0
  have hi : (fun i=>Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool)
      (RecoveryPCPFormulaResumeCount.input R) (fun _=>List.replicate 0 false) i)=input R := rfl
  rw [hi] at hr
  have hb : 2*base.steps+2≤budget R := by unfold budget; omega
  have hmore:=run_moreFuel readyMachine _ (budget R-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨r.final.tapes,⟨r,hmore,rfl,rh,by omega⟩,(rt 0).trans b0,(rt 4).trans b4⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCountCold

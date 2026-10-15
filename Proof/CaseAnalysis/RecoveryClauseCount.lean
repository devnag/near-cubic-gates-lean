import Proof.MachineModel.OrdinaryMatrixPacketOffset
import Proof.MachineModel.UWalkUnary

/-! The original normalization clause counter starts at its paid head one.
One left move and the existing unary copier supply the actual metadata count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdClauseCount
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 1→Fin 3:=fun _=>0
def first:=RecoveryFocus.machine slots (MatrixPacketOffset.move .left)
def machine:=Composition.machine first (UWalkUnary.machine false false)
def heads : Fin 3→ℕ:=![1,0,0]
def input (n : ℕ) : Fin 3→List Bool:=![CompareMachine.word n,[],[]]
def output (n : ℕ) : Fin 3→List Bool:=
  ![CompareMachine.word n,List.replicate n true,List.replicate (n+2) false]
def budget (n : ℕ):=2*n+8

theorem count_run (n : ℕ) : ∃ r,
    runFrom machine (budget n) ⟨machine.start,heads,input n⟩=some r ∧
      r.steps≤budget n ∧ r.final.heads=(fun _=>0) ∧ r.final.tapes=output n := by
  obtain ⟨pre,hp,hpf,hps⟩:=MatrixPacketOffset.move_run .left (CompareMachine.word n) 1
  obtain ⟨a,ha,haf,has⟩:=RecoveryFocus.run_config slots (by decide)
    (MatrixPacketOffset.move .left) heads (input n) _ _ pre hp
  have hi : RecoveryFocus.config slots heads (input n)
      (MatrixPacketOffset.moveCfg 0 (CompareMachine.word n) 1)=⟨first.start,heads,input n⟩ := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [RecoveryFocus.config,RecoveryFocus.pick,slots,heads,MatrixPacketOffset.moveCfg]
    · funext i;fin_cases i <;>simp [RecoveryFocus.config,RecoveryFocus.pick,slots,input,MatrixPacketOffset.moveCfg]
  rw [hi] at ha
  have ah : a.final.heads=(fun _=>0) := by
    rw [haf,hpf]
    funext i;fin_cases i <;>simp [RecoveryFocus.config,RecoveryFocus.pick,slots,heads,MatrixPacketOffset.moveCfg,HeadMove.apply]
  have atapes : a.final.tapes=input n := by
    rw [haf,hpf]
    funext i;fin_cases i <;>simp [RecoveryFocus.config,RecoveryFocus.pick,slots,input,MatrixPacketOffset.moveCfg]
  have hu : ClockJoin.ReadyRun (UWalkUnary.machine false false) (2*n+6) (input n) (output n) := by
    simpa [input,output,UWalkUnary.input,UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad_zero,
      UWalkUnary.output,UWalkUnary.lead] using UWalkUnary.ready false false 0 n
  obtain ⟨b,hb,bt,bh,bs⟩:=hu
  have he : Composition.restart a.final (UWalkUnary.machine false false).start=
      initialConfiguration (UWalkUnary.machine false false) (input n) :=
    configuration_ext rfl ah atapes
  have hb' : runFrom (UWalkUnary.machine false false) (2*n+6)
      (Composition.restart a.final (UWalkUnary.machine false false).start)=some b := by
    rw [he];exact hb
  have hj:=Composition.run_join first (UWalkUnary.machine false false) 1 (2*n+6) _ a b ha hb'
  have hc : 1+1+(2*n+6)=budget n:=by unfold budget;omega
  rw [hc] at hj
  exact ⟨Composition.joinedReceipt a b,hj,by change a.steps+1+b.steps≤budget n;unfold budget;omega,funext bh,bt⟩

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdClauseCount

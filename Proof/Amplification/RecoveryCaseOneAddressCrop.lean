import Proof.Amplification.RecoveryCaseOneOrdinaryFunction
import Proof.Amplification.RecoveryFieldCopy

/-! The target address is physically cropped by the generated core's
actual unary arity. The trailing sentinel is part of the supplied scalar. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneAddressCrop
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def padding (width : Nat) : Fin 4→Nat := ![0,0,width+2,0]
def input (address : List Bool) (width : Nat) : Fin 4→List Bool :=
  ![frame address,[],UnaryTemplate.tape width,[]]
def output (address : List Bool) (width : Nat) : Fin 4→List Bool :=
  ![frame address,frame (address.take width),UnaryTemplate.tape width,List.replicate (4*width+4) false]

theorem template (width : Nat) :
    ZeroPadding.pad (width+2) (CompareMachine.word width)=UnaryTemplate.tape width := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem ready (address : List Bool) (width : Nat) (hw : width≤address.length) :
    ClockJoin.ReadyRun RecoveryFieldCopy.machine (8*width+10) (input address width) (output address width) := by
  obtain ⟨base,hb,bt,bh,bs⟩:=RecoveryFieldCopy.take_ready address [] width 0 hw (by simp)
  obtain ⟨actual,ha,hf,hs,_⟩:=ZeroPadding.run_config RecoveryFieldCopy.machine (padding width) _ _ base hb
  have hi : ZeroPadding.config (padding width)
      (initialConfiguration RecoveryFieldCopy.machine
        ![frame address,[],CompareMachine.word width,List.replicate 0 false])=
      initialConfiguration RecoveryFieldCopy.machine (input address width) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,padding,initialConfiguration,input,template]
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.le.trans bs.le⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,bt,padding,output,template]
  · intro i
    rw [hf]
    exact bh i

end
end NearCubicWires.RepairSource.RecoveryCaseOneAddressCrop

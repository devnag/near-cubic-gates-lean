import Proof.MachineModel.OrdinaryMatrixPacketCapacityEndpoint

/-! Restore the original framed request into an actually erased packet
workspace. Only the destination is zero padded; the external canonical
source and its reusable copy counters are retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketRequestCopy
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) (cap left right : ℕ) : Fin 4 → List Bool :=
  ![frame bits,List.replicate cap false,List.replicate left false,List.replicate right false]
def output (bits : List Bool) (cap left right : ℕ) : Fin 4 → List Bool :=
  ![frame bits,ZeroPadding.pad cap (frame bits),List.replicate (max left (2*bits.length+1)) false,
    List.replicate (max right (4*bits.length+3)) false]

theorem copy_ready (bits : List Bool) (cap left right : ℕ) :
    ReadyRun RecoveryRootRound.copyMachine (8*bits.length+8) (input bits cap left right) (output bits cap left right) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := RecoveryRootRound.copy_ready bits [] left right (by simp)
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config RecoveryRootRound.copyMachine (![0,cap,0,0] : Fin 4 → ℕ) _ _ base hb
  have hi : ZeroPadding.config (![0,cap,0,0] : Fin 4 → ℕ)
      (initialConfiguration RecoveryRootRound.copyMachine ![frame bits,[],List.replicate left false,List.replicate right false])=
      initialConfiguration RecoveryRootRound.copyMachine (input bits cap left right) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,ZeroPadding.pad,input,initialConfiguration]
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,bt,output]
  · intro i
    exact (congrArg (fun c => c.heads i) hf).trans (bh i)

end NearCubicWires.RepairOrdinary.MatrixPacketRequestCopy

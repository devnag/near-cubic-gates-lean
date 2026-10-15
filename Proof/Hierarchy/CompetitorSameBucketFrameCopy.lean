import Proof.Hierarchy.CompetitorSameBucketWorkspace

/-! Copy a physically retained exact frame into the already allocated C
backing, restoring both existing C logs. The source need not be padded. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdFrameCopy
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (cap : ℕ) : Fin 4 → ℕ := ![0,cap,0,0]
def input (bits : List Bool) (cap : ℕ) : Fin 4 → List Bool :=
  ![frame bits,List.replicate cap false,List.replicate cap false,List.replicate cap false]
def output (bits : List Bool) (cap : ℕ) : Fin 4 → List Bool :=
  ![frame bits,ZeroPadding.pad cap (frame bits),List.replicate cap false,List.replicate cap false]

theorem copy_ready (bits : List Bool) (cap : ℕ) (hc : 4*bits.length+3≤cap) :
    ReadyRun RecoveryRootRound.copyMachine (8*bits.length+8) (input bits cap) (output bits cap) := by
  obtain ⟨base,hb,bt,bh,bs⟩:=RecoveryRootRound.copy_ready bits [] cap cap (by simp)
  have hc' : 2*bits.length+1≤cap := by omega
  simp only [max_eq_left hc,max_eq_left hc'] at bt
  obtain ⟨actual,ha,hf,hs,_⟩:=ZeroPadding.run_config RecoveryRootRound.copyMachine (padding cap) _ _ base hb
  have hi : ZeroPadding.config (padding cap)
      (initialConfiguration RecoveryRootRound.copyMachine
        ![frame bits,[],List.replicate cap false,List.replicate cap false])=
      initialConfiguration RecoveryRootRound.copyMachine (input bits cap) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,padding,initialConfiguration,input,ZeroPadding.pad]
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,bt,padding,output,ZeroPadding.pad]
  · intro i
    rw [hf]
    exact bh i

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdFrameCopy

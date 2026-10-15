import Proof.Amplification.RecoveryBoundedTapeCopy

/-! Reload a short degree template into the already erased C-cell work tape.
The existing bounded copy reads exactly C cells; both its driver and log are
retained. This cost belongs entirely to additive row preparation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsMetadataCopy
open LocalBitMultitape RecoveryRootRound RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_self (source : List Bool) : copied source source.length=source := by
  apply List.ext_getElem
  · simp
  · intro i _hi hj
    simp [copied,readTapeBit,List.getD,hj]

theorem copied_pad (source : List Bool) (C : ℕ) (hc : source.length≤C) :
    copied source C=ZeroPadding.pad C source := by
  have hp : (ZeroPadding.pad C source).length=C := by simp [hc]
  have h := copied_self (ZeroPadding.pad C source)
  rw [hp] at h
  have he : readTapeBit (ZeroPadding.pad C source)=readTapeBit source :=
    funext (ZeroPadding.read_pad C source)
  simpa only [copied,he] using h

def input (source : List Bool) (C : ℕ) : Fin 4→List Bool :=
  ![source,List.replicate C false,List.replicate C true,List.replicate (C+1) false]
def output (source : List Bool) (C : ℕ) : Fin 4→List Bool :=
  ![source,ZeroPadding.pad C source,List.replicate C true,List.replicate (C+1) false]

theorem copy_ready (source : List Bool) (C : ℕ) (hc : source.length≤C) :
    ReadyRun RecoveryBoundedTapeCopy.machine (2*C+4) (input source C) (output source C) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := RecoveryBoundedTapeCopy.copy_ready source C (C+1)
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config RecoveryBoundedTapeCopy.machine
    (![0,C,0,0] : Fin 4→ℕ) _ _ base hb
  have hi : ZeroPadding.config (![0,C,0,0] : Fin 4→ℕ)
      (initialConfiguration RecoveryBoundedTapeCopy.machine
        ![source,[],List.replicate C true,List.replicate (C+1) false])=
      initialConfiguration RecoveryBoundedTapeCopy.machine (input source C) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,input,ZeroPadding.pad]
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,bt,output,copied_pad source C hc,
      ZeroPadding.pad,hc]
  · intro i
    rw [hf]
    exact bh i

end NearCubicWires.RepairOrdinary.CloseoutRowsMetadataCopy

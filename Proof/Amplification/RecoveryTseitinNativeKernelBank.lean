import Proof.Amplification.RecoveryTseitinNativeKernelLayout

/-! Allocate or clear the actual node-clause scratch from the retained paid
capacity driver, keeping the formula cursor and original source untouched. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def kernelBankMachine := RecoveryFocus.machine kernelBankSlots (RecoveryScratchErase.resetMachine 235)
theorem kernel_bank_run {z : Nat} (cap : Nat) (backing : Fin 235→List Bool) (ambient : Configuration 1335 z)
    (hb : ∀ i,(backing i).length≤cap)
    (hh : ∀ i,ambient.heads (kernelBankSlots i)=0)
    (hw : ∀ i,ambient.tapes (kernelWork i)=backing i)
    (hd : ambient.tapes 17=List.replicate cap true)
    (hl : ambient.tapes 18=List.replicate (cap+1) false) :
    ∃ r,runFrom kernelBankMachine (2*cap+4) (Composition.restart ambient kernelBankMachine.start)=some r ∧
      (∀ i,r.final.tapes (kernelWork i)=List.replicate cap false) ∧
      r.final.tapes 17=List.replicate cap true ∧ r.final.tapes 18=List.replicate (cap+1) false ∧
      (∀ i,r.final.heads (kernelBankSlots i)=0) ∧ r.steps≤2*cap+4 ∧
      (∀ i,(∀ j,kernelBankSlots j≠i) → r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) := by
  obtain ⟨base,hbase,bt,bh,bs⟩:=RecoveryScratchErase.erase_ready cap (cap+1) backing hb
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩:=RecoveryFocus.dock kernelBankSlots kernel_bank_injective
    (RecoveryScratchErase.resetMachine 235) _ ambient.heads ambient.tapes _ hh
    (by
      intro i
      refine Fin.addCases (m:=236) (n:=1) (fun a=>?_) (fun a=>?_) i
      · refine Fin.addCases (m:=235) (n:=1) (fun b=>?_) (fun b=>?_) a
        · simpa only [kernelBankSlots,Fin.addCases_left,initialConfiguration] using hw b
        · fin_cases b; exact hd
      · fin_cases a; exact hl) base hbase
  refine ⟨r,hr,?_,?_,?_,?_,(rs.trans bs).le,?_⟩
  · intro i
    have h:=rt ((i.castAdd 1).castAdd 1)
    rw [bt] at h
    simpa only [kernelBankSlots,Fin.addCases_left] using h
  · have h:=rt ((0 : Fin 1).natAdd 235 |>.castAdd 1)
    rw [bt] at h
    exact h
  · have h:=rt ((0 : Fin 1).natAdd 236)
    rw [bt] at h
    simpa only [kernelBankSlots,Fin.addCases_right,max_self] using h
  · intro i
    exact (rh i).trans (bh i)
  · intro i hi
    have h:=ro i hi
    exact ⟨h.2,h.1⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative

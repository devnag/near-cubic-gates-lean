import Proof.Amplification.RecoveryTseitinNativeKernelViewActual
import Proof.Amplification.RecoveryTseitinNativeKernelBank

/-! The paid physical allocator supplies the exact original node consumer,
retaining its native source, parsed tag and real append cursor. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RecoveryTseitinNode RecoveryTseitinKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem allocated_run {n z : Nat} (index : Nat) (node : BooleanNode n) (out : List Bool)
    (ambient : Configuration 1335 z)
    (href : ∀ k,ambient.tapes (generatedRef k)=RecoveryTseitinReferences.fields n index
      (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2) k ∧
      ambient.heads (generatedRef k)=0)
    (hd : ambient.tapes 17=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) true)
    (hl : ambient.tapes 18=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (n+index)+1) false)
    (hdh : ambient.heads 17=0) (hlh : ambient.heads 18=0)
    (hw : ∀ i,ambient.tapes (kernelWork i)=[] ∧ ambient.heads (kernelWork i)=0)
    (hout : ambient.tapes 1333=out) (houth : ambient.heads 1333=out.length) :
    ∃ r,runFrom kernelBankMachine (2*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+4)
      (Composition.restart ambient kernelBankMachine.start)=some r ∧
      (∀ i,r.final.tapes (kernelSlots (decide (kind node=2)) i)=
        RecoveryTseitinClauseAppend.input (readyData index node) out (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) i ∧
        r.final.heads (kernelSlots (decide (kind node=2)) i)=RecoveryTseitinClauseAppend.heads out.length i) ∧
      (∀ i,(19 ≤ i.val ∧ i.val < 1099) → r.final.tapes i=ambient.tapes i ∧ r.final.heads i=ambient.heads i) ∧
      r.steps ≤ 2*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+4 := by
  have hhead : ∀ i,ambient.heads (kernelBankSlots i)=0 := by
    intro i
    refine Fin.addCases (m:=236) (n:=1) (fun a=>?_) (fun a=>?_) i
    · refine Fin.addCases (m:=235) (n:=1) (fun b=>?_) (fun b=>?_) a
      · simpa only [kernelBankSlots,Fin.addCases_left] using (hw b).2
      · fin_cases b; exact hdh
    · fin_cases a; exact hlh
  obtain ⟨r,hr,rw,rd,rl,rh,rs,keep⟩:=kernel_bank_run
    (RecoveryTseitinTautology.Cold.driverCapacity (n+index)) (fun _=>[]) ambient
    (by intro i; exact Nat.zero_le _) hhead (fun i=>(hw i).1) hd hl
  refine ⟨r,hr,?_,?_,rs⟩
  · apply kernel_view index node out r.final
    · intro j
      have hk:= (referencePorts (kind node) j).isLt
      have ha : (generatedRef (referencePorts (kind node) j)).val < 17 := by
        change 10+(referencePorts (kind node) j).val < 17
        omega
      have h:=keep _ (bank_away _ (Or.inl ha))
      exact ⟨h.1.trans (href _).1,h.2.trans (href _).2⟩
    · exact rd
    · exact rl
    · exact rh ((0 : Fin 1).natAdd 235 |>.castAdd 1)
    · exact rh ((0 : Fin 1).natAdd 236)
    · intro i
      refine ⟨rw i,?_⟩
      simpa only [kernelBankSlots,Fin.addCases_left] using rh ((i.castAdd 1).castAdd 1)
    · exact (keep 1333 (bank_away _ (Or.inr (Or.inr rfl)))).1.trans hout
    · exact (keep 1333 (bank_away _ (Or.inr (Or.inr rfl)))).2.trans houth
  · intro i hi
    exact keep i (bank_away i (Or.inr (Or.inl hi)))

end NearCubicWires.RepairSource.RecoveryTseitinNative

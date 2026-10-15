import Proof.MachineModel.BankCountRaw

/-! The existing zero-polynomial worker uses the same enlarged bank and
leaves every private converter tape untouched. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def zero:=RecoveryFocus.machine rawOld BankZero.machine

theorem zero_run (B C : ℕ) (hB : B≤C) (out pre tail : List Bool)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes C B (pre++[false]++tail) [] 0 j)
    (hheads : ∀ i,H (old i)=CloseoutRowsBankFields.heads out i)
    (hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length≤C)
    (ho : A 31=out) (hd : A 104=List.replicate C true)
    (hl : A 105=List.replicate (C+1) false) :
    ∃ result,runFrom zero (BankZero.budget B C) ⟨zero.start,H,A⟩=some result ∧
      result.steps≤BankZero.budget B C ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads out i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C out i) ∧
      result.final.heads 113=pre.length+1 ∧ result.final.tapes 113=A 113 ∧
      result.final.heads 115=0 ∧ result.final.tapes 115=List.replicate C false:=by
  obtain ⟨base,hb,_bs,bh,bt,bpos,bsource,bcount,bzero⟩:=BankZero.zero_run B C hB out pre tail
    (H ∘ rawOld) (A ∘ rawOld) hh ht hheads hsize ho hd hl
  obtain ⟨result,hr,_rf,_rs,rh,rt,_keep⟩:=RecoveryFocus.dock rawOld rawOld_injective BankZero.machine
    _ H A _ (fun _=>rfl) (fun _=>rfl) base hb
  refine ⟨result,hr,runFrom_steps_le zero _ _ _ hr,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (rh (BankConsumer.old i)).trans (bh i)
  · intro i
    exact (rt (BankConsumer.old i)).trans (bt i)
  · exact (rh 113).trans bpos
  · exact (rt 113).trans bsource
  · exact (rh 115).trans bcount
  · exact (rt 115).trans bzero

end NearCubicWires.ExtIncidence.BankCount

import Proof.Amplification.RecoveryTseitinIncrement

/-! One complete ordinary iteration emits the original tautology, advances
its physical binary index, and leaves the same scratch bank reusable. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Valid (cap index : Nat) (data : Fin 239→List Bool) : Prop where
  indexTape : data 0=ZeroPadding.pad cap (RepairOrdinary.frame index.bits)
  driver : data 3=List.replicate cap true
  log : data 4=List.replicate (cap+1) false
  bounded : Bounded cap data

def word (index : Nat) := (Encodable.encode (circuitInputTautology index)).bits
noncomputable def bodyMachine := Composition.machine emitMachine incrementMachine
def bodyBudget (cap : Nat) := 24*cap+16

theorem valid_update (cap index : Nat) (data : Fin 239→List Bool)
    (hd : data 3=List.replicate cap true) (hl : data 4=List.replicate (cap+1) false)
    (hb : Bounded cap data) :
    Valid cap index (Function.update data 0 (ZeroPadding.pad cap (RepairOrdinary.frame index.bits))) := by
  refine ⟨by simp,by simpa using hd,by simpa using hl,?_⟩
  intro i hi
  have hn : i≠0 := by intro he; have hh:=congrArg Fin.val he; change i.val=0 at hh; omega
  simpa only [Function.update_of_ne hn] using hb i hi

theorem input_update (cap : Nat) (data : Fin 239→List Bool) (out bits : List Bool) :
    Function.update (input data out cap) 0 bits=input (Function.update data 0 bits) out cap := by
  funext i
  refine Fin.addCases (m:=239) (n:=2) (fun j=>?_) (fun j=>?_) i
  · by_cases hj : j=0
    · subst j; rfl
    have hn : (j.castAdd 2 : Fin 241)≠0 := by intro he; apply hj; exact Fin.ext (congrArg (fun i : Fin 241=>i.val) he)
    simp only [Function.update_of_ne hn,input,Fin.addCases_left,Function.update_of_ne hj]
  · fin_cases j <;> rfl

theorem body_run (cap index : Nat) (ambient : Fin 239→List Bool) (out : List Bool)
    (hcap : capacity index ≤ cap) (hv : Valid cap index ambient) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom bodyMachine (bodyBudget cap)
        ⟨bodyMachine.start,heads out.length,input ambient out cap⟩=some r ∧
      r.final.heads=heads (out++RepairOrdinary.frame (word index)).length ∧
      r.final.tapes=input after (out++RepairOrdinary.frame (word index)) cap ∧
      Valid cap (index+1) after ∧
      (∀ i : Fin 239,1 ≤ i.val → i.val<3 → after i=ambient i) ∧ r.steps ≤ bodyBudget cap := by
  have hi := (RecoveryTseitin.argument_widths (Prepare.literals signs (fun _=>index)) 0).2
  change index.bits.length ≤ RecoveryTseitin.width (Prepare.literals signs (fun _=>index)) at hi
  have hw : RecoveryTseitin.width (Prepare.literals signs (fun _=>index))+1 ≤
      (RecoveryTseitin.width (Prepare.literals signs (fun _=>index))+1)^2 := by nlinarith
  have hwork : ClockIncrement.work index.bits ≤ cap := by
    have hc := ClockIncrement.work_bound index.bits
    unfold capacity RecoveryTseitin.capacity at hcap
    omega
  have hbits : index.bits.length ≤ cap := by
    unfold capacity RecoveryTseitin.capacity at hcap
    omega
  obtain ⟨encoded,first,hr,fh,ft,hkeep,hd,hl,hb,fs⟩ := emit_run cap (cap+1) index ambient
    (List.replicate (cap-(RepairOrdinary.frame index.bits).length) false) out hcap hv.bounded hv.driver hv.log
    (Nat.le_refl _) hv.indexTape
  obtain ⟨last,lr,lh,lt,ls⟩ := increment_run cap index first.final.heads first.final.tapes hwork
    (by rw [fh]; rfl) (by rw [fh]; rfl)
    (by rw [ft]; exact (hkeep 0 (by decide)).trans hv.indexTape) (by rw [ft]; rfl)
  let after := Function.update encoded 0 (ZeroPadding.pad cap (RepairOrdinary.frame (index+1).bits))
  have hvalid : Valid cap (index+1) after := valid_update cap (index+1) encoded hd hl hb
  have hall := Composition.run_join emitMachine incrementMachine _ _ _ first last hr lr
  have htime : (20*cap+4)+1+(4*index.bits.length+8) ≤ bodyBudget cap := by unfold bodyBudget; omega
  have hmore := runFrom_moreFuel bodyMachine _
    (bodyBudget cap-((20*cap+4)+1+(4*index.bits.length+8))) _ _ hall
  rw [Nat.add_sub_of_le htime] at hmore
  refine ⟨after,_,hmore,lh.trans fh,?_,hvalid,?_,?_⟩
  · change last.final.tapes=_
    rw [lt,ft,input_update]
    rfl
  · intro i hi hit
    have hn : i≠0 := by intro he; have hh:=congrArg Fin.val he; change i.val=0 at hh; omega
    simpa [after,Function.update_of_ne hn] using hkeep i hit
  · change first.steps+1+last.steps ≤ bodyBudget cap
    omega

end NearCubicWires.RepairSource.RecoveryTseitinTautology

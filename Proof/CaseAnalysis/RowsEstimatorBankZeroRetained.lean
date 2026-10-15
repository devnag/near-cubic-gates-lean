import Proof.MachineModel.BankCountOptional

/-! The empty raw stream has no polynomial call. Its actual incidence run and
paid clear return the same native bank; no unrelated metadata is required. -/
namespace NearCubicWires.ExtIncidence.BankZero
open LocalBitMultitape RepairOrdinary BankConsumer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem zero_retained_run (B C : ℕ) (hB : B ≤ C) (out pre tail : List Bool)
    (H : Fin 116 → ℕ) (A : Fin 116 → List Bool)
    (hh : ∀ j,H (BankExecution.slots j)=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (BankExecution.slots j)=Padded.tapes C B (pre++[false]++tail) [] 0 j)
    (hheads : ∀ i,H (old i)=CloseoutRowsBankFields.heads out i)
    (hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length ≤ C)
    (ho : A 31=out) (hd : A 104=List.replicate C true)
    (hl : A 105=List.replicate (C+1) false) :
    ∃ result,runFrom machine (budget B C) ⟨machine.start,H,A⟩=some result ∧
      result.steps ≤ 6*C+14 ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads out i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C out i) ∧
      result.final.heads 113=pre.length+1 ∧ result.final.tapes 113=A 113 ∧
      result.final.heads 115=0 ∧ result.final.tapes 115=List.replicate C false ∧
      result.final.heads 114=H 114 ∧ result.final.tapes 114=A 114 := by
  let ms : List (List (Fin B)):=[]
  let nextH:=BankExecution.changedHeads H (pre.length+1) 0 0
  have htable:A 36=ZeroPadding.pad C []:=ht 3
  have hcount:A 115=ZeroPadding.pad C []:=ht 4
  have tapes:BankExecution.changedTapes A C [] 0=A:=by
    rw [BankExecution.changedTapes,←htable]
    simp only [Function.update_eq_self,List.replicate_zero,←hcount]
  have first:=BankExecution.raw_run ms C hB pre tail H A hh ht
    (by simp [ms,rawRows]) (by simp [ms]) (hheads 104) (hheads 105) hd hl
  simp only [ms,rawIndices,List.map_nil,rawRows,List.flatten_nil,stream,List.flatMap_nil,
    List.nil_append,List.length_singleton,List.length_nil,tapes] at first
  have bankH:∀ i,nextH (old i)=CloseoutRowsBankFields.heads out i:=by
    intro i
    by_cases h36:i=36
    · subst i
      simp [nextH,BankExecution.changedHeads,old,CloseoutRowsBankFields.heads,CloseoutRowsBankFields.raised]
    · have n36:old i≠36:=by intro he;exact h36 (Fin.ext (congrArg (fun k : Fin 116=>k.val) he))
      simpa only [nextH,BankExecution.changedHeads,Function.update_of_ne (old_ne i 115 (by decide)),
        Function.update_of_ne n36,Function.update_of_ne (old_ne i 113 (by decide))] using hheads i
  obtain ⟨base,hbase,bh,bt,bo,bs⟩:=CloseoutRowsBankClear.clear_run C out (fun i=>A (old i)) hsize hd hl
  obtain ⟨last,hlast,_lf,ls,lh,lt,keep⟩:=RecoveryFocus.dock old old_injective
    CloseoutRowsBankClear.machine _ nextH A _ bankH (fun _=>rfl) base hbase
  obtain ⟨result,hr,rh,rt,rs⟩:=PCPOuter.exact_then first last hlast
  refine ⟨result,hr,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rs,ls]
    unfold BankExecution.budget CloseoutRowsBankClear.budget cost at *
    simp only [List.map_nil,List.sum_nil] at *
    omega
  · intro i;rw [rh,lh,bh]
  · intro i
    rw [rt,lt,CloseoutRowsBankPorts.erased_store C out base.final.tapes (bo.trans ho) bt]
  · rw [rh,(keep 113 (fun i=>old_ne i 113 (by decide))).1]
    simp only [nextH,BankExecution.changedHeads,Function.update_of_ne (by decide : (113 : Fin 116)≠115),
      Function.update_of_ne (by decide : (113 : Fin 116)≠36),Function.update_self]
  · rw [rt,(keep 113 (fun i=>old_ne i 113 (by decide))).2]
  · rw [rh,(keep 115 (fun i=>old_ne i 115 (by decide))).1]
    exact Function.update_self _ _ _
  · rw [rt,(keep 115 (fun i=>old_ne i 115 (by decide))).2,hcount]
    simp [ZeroPadding.pad]

  · rw [rh,(keep 114 (fun i=>old_ne i 114 (by decide))).1]
    simp [nextH,BankExecution.changedHeads]
  · rw [rt,(keep 114 (fun i=>old_ne i 114 (by decide))).2]

end NearCubicWires.ExtIncidence.BankZero

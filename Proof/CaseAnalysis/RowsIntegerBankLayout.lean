import Proof.CaseAnalysis.CloseoutRowsIntegerLoop

/-! The integer stream starts with its actual capacity driver and retained
source/output. One sweep allocates all local cells, including the load log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 217) : Fin 220:=
  if i.val=213 then 214 else if i.val=214 then 218 else ⟨i.val,by omega⟩
def work (i : Fin 215):=slots (i.castAdd 2)
theorem slot_val (i : Fin 217) : (slots i).val=if i.val=213 then 214 else if i.val=214 then 218 else i.val:=by
  unfold slots
  split_ifs <;> rfl
theorem slots_injective : Function.Injective slots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [slot_val,slot_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem slots_retained (i : Fin 217) : slots i≠213 ∧ slots i≠217 ∧ slots i≠219:=by
  have hv:=slot_val i
  split_ifs at hv
  all_goals
    refine ⟨?_,?_,?_⟩ <;> intro h <;> have he:=congrArg Fin.val h <;> omega
theorem work_not_driver (i : Fin 215) : work i≠215:=by
  intro h
  have hv:=congrArg Fin.val h
  simp only [work,slot_val,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega
theorem work_core (i : Fin 214) : work (i.castAdd 1)=CloseoutRowsIntegerRound.scratchSlots i:=by
  apply Fin.ext
  simp only [work,slot_val,Fin.val_castAdd,CloseoutRowsIntegerRound.scratchSlots,
    CloseoutRowsIntegerRound.erase_val]
  split_ifs <;> omega

def input (cap : ℕ) (out source : List Bool) (flag : Bool) (i : Fin 220):=
  if i=213 then out else if i=215 then List.replicate cap true
    else if i=217 then source else if i=219 then [flag] else []
noncomputable def erased (cap : ℕ) (out source : List Bool) (flag : Bool):=
  install slots (input cap out source flag) (PCPTraversal.clearedLocal 215 cap (cap+1))

theorem input_work (cap : ℕ) (out source : List Bool) (flag : Bool) (i : Fin 215) :
    input cap out source flag (work i)=[]:=by
  have h:work i≠213 ∧ work i≠217 ∧ work i≠219:=slots_retained (i.castAdd 2)
  simp only [input,if_neg h.1,if_neg (work_not_driver i),if_neg h.2.1,if_neg h.2.2]

theorem erased_work (cap : ℕ) (out source : List Bool) (flag : Bool) (i : Fin 215) :
    erased cap out source flag (work i)=List.replicate cap false:=by
  have h:=install_slot slots slots_injective (input cap out source flag)
    (PCPTraversal.clearedLocal 215 cap (cap+1)) ((i.castAdd 1).castAdd 1)
  have he:(i.castAdd 1).castAdd 1=i.castAdd 2:=Fin.ext rfl
  have hout:PCPTraversal.clearedLocal 215 cap (cap+1) ((i.castAdd 1).castAdd 1)=List.replicate cap false:=by
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
  rw [hout] at h
  simpa only [erased,work,he] using h
theorem erased_driver (cap : ℕ) (out source : List Bool) (flag : Bool) :
    erased cap out source flag 215=List.replicate cap true:=
  install_slot slots slots_injective _ _ 215
theorem erased_log (cap : ℕ) (out source : List Bool) (flag : Bool) :
    erased cap out source flag 216=List.replicate (cap+1) false:=by
  have h:=install_slot slots slots_injective (input cap out source flag)
    (PCPTraversal.clearedLocal 215 cap (cap+1)) ((0 : Fin 1).natAdd 216)
  have he:slots ((0 : Fin 1).natAdd 216)=(216 : Fin 220):=by decide
  simpa only [erased,he,PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self] using h
theorem erased_retained (cap : ℕ) (out source : List Bool) (flag : Bool) (i : Fin 220)
    (hi : i=213 ∨ i=217 ∨ i=219) :
    erased cap out source flag i=input cap out source flag i:=by
  apply install_other
  intro j
  rcases hi with rfl|rfl|rfl
  · exact (slots_retained j).1
  · exact (slots_retained j).2.1
  · exact (slots_retained j).2.2

theorem erased_data (cap : ℕ) (out source : List Bool) (flag : Bool) (hcap : 1≤cap) :
    erased cap out source flag=CloseoutRowsIntegerRound.data cap [] out source flag:=by
  funext i
  refine Fin.addCases (m:=215) (n:=5) ?_ ?_ i
  · intro j
    simp only [CloseoutRowsIntegerRound.data,Fin.addCases_left]
    by_cases hj:j=213
    · subst j
      exact erased_retained cap out source flag 213 (Or.inl rfl)
    · have hz:CloseoutRowsIntegerRound.coreTapes cap [] out j=List.replicate cap false:=by
        simp only [CloseoutRowsIntegerRound.coreTapes,if_neg hj]
        split_ifs
        · exact CloseoutRowsIntegerReady.pad_empty_frame cap hcap
        · rfl
      rw [hz]
      obtain ⟨k,hk⟩:=CloseoutRowsIntegerRound.scratch_covers j hj
      change erased cap out source flag (CloseoutRowsIntegerRound.coreSlots j)=_
      rw [←hk,←work_core,erased_work]
  · intro j
    fin_cases j
    · exact erased_driver cap out source flag
    · exact erased_log cap out source flag
    · exact erased_retained cap out source flag 217 (Or.inr (Or.inl rfl))
    · exact erased_work cap out source flag 214
    · exact erased_retained cap out source flag 219 (Or.inr (Or.inr rfl))

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerBank

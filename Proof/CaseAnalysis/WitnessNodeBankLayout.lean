import Proof.CaseAnalysis.WitnessDAGBounds
import Proof.CaseAnalysis.RowsMetadataCopy

/-! The initial node bank is physically cleared once and its four retained
metadata words are copied into the resulting backing. The raw field stream
and its validity bit lie outside every allocation/copy slot. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlot (i : Fin 750) : Fin 759:=
  if i.val<747 then ⟨i.val,by omega⟩
  else if i.val=747 then 748 else ⟨i.val+4,by omega⟩
def sweepSlot : Fin 752→Fin 759:=
  Fin.addCases (motive:=fun _ : Fin (750+2)=>Fin 759) workSlot (fun i : Fin 2=>![749,750] i)
def common (j : Fin 4) : Fin 759:=⟨668+j.val,by omega⟩
def field (j : Fin 4) : Fin 759:=j.natAdd 755
def copySlots (j : Fin 4) : Fin 4→Fin 759:=![field j,common j,749,750]

theorem work_val (i : Fin 750) : (workSlot i).val=
    if i.val<747 then i.val else if i.val=747 then 748 else i.val+4:=by
  unfold workSlot
  split_ifs <;> rfl
theorem work_small (i : Fin 750) : (workSlot i).val<754:=by
  rw [work_val]
  split_ifs <;> omega
theorem work_avoids (i : Fin 750) :
    workSlot i≠747 ∧ workSlot i≠749 ∧ workSlot i≠750 ∧ workSlot i≠751:=by
  have hv:=work_val i
  split_ifs at hv
  all_goals
    refine ⟨?_,?_,?_,?_⟩ <;> intro h <;>
      have he:=congrArg Fin.val h <;> omega
theorem work_injective : Function.Injective workSlot:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [work_val,work_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem sweep_injective : Function.Injective sweepSlot:=by
  intro a b
  refine Fin.addCases (m:=750) (n:=2) ?_ ?_ a
  · intro i
    refine Fin.addCases (m:=750) (n:=2) ?_ ?_ b
    · intro j h
      simp only [sweepSlot,Fin.addCases_left] at h
      exact congrArg (Fin.castAdd 2) (work_injective h)
    · intro j h
      simp only [sweepSlot,Fin.addCases_left,Fin.addCases_right] at h
      fin_cases j
      · exact False.elim ((work_avoids i).2.1 h)
      · exact False.elim ((work_avoids i).2.2.1 h)
  · intro i
    refine Fin.addCases (m:=750) (n:=2) ?_ ?_ b
    · intro j h
      simp only [sweepSlot,Fin.addCases_left,Fin.addCases_right] at h
      fin_cases i
      · exact False.elim ((work_avoids j).2.1 h.symm)
      · exact False.elim ((work_avoids j).2.2.1 h.symm)
    · intro j h
      fin_cases i <;> fin_cases j <;> simp [sweepSlot,Fin.addCases] at h ⊢
theorem common_injective : Function.Injective common:=by
  intro a b h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  change 668+a.val=668+b.val at hv
  omega
theorem copy_injective (j : Fin 4) : Function.Injective (copySlots j):=by
  intro a b h
  have hv:=congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [copySlots,field,common] at hv ⊢ <;> omega
theorem sweep_common (j : Fin 4) :
    sweepSlot ((⟨668+j.val,by omega⟩ : Fin 750).castAdd 2)=common j:=by
  simp only [sweepSlot,Fin.addCases_left,workSlot,show 668+j.val<747 by omega,if_true]
  rfl
theorem sweep_field (j : Fin 4) (i : Fin 752) : sweepSlot i≠field j:=by
  refine Fin.addCases (m:=750) (n:=2) ?_ ?_ i
  · intro k h
    have hv:=congrArg Fin.val h
    simp only [sweepSlot,Fin.addCases_left,field,Fin.val_natAdd] at hv
    have hs:=work_small k
    omega
  · intro k h
    simp only [sweepSlot,Fin.addCases_right] at h
    fin_cases k
    · have hv:(749 : ℕ)=755+j.val:=congrArg Fin.val h
      omega
    · have hv:(750 : ℕ)=755+j.val:=congrArg Fin.val h
      omega

def input (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) : Fin 759→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (755+4)=>List Bool)
    (fun i : Fin 755=>if i=749 then List.replicate cap true
      else if i=751 then source else if i=754 then [flag] else []) fields
noncomputable def erased (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool):=
  install sweepSlot (input cap fields source flag) (PCPTraversal.clearedLocal 750 cap (cap+1))
noncomputable def bank (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ):=
  install common (erased cap fields source flag)
    (fun j=>if j.val<k then ZeroPadding.pad cap (fields j) else List.replicate cap false)

theorem erased_common (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (j : Fin 4) :
    erased cap fields source flag (common j)=List.replicate cap false:=by
  rw [←sweep_common j,erased,install_slot _ sweep_injective]
  rw [show ((⟨668+j.val,by omega⟩ : Fin 750).castAdd 2)=
    (((⟨668+j.val,by omega⟩ : Fin 750).castAdd 1).castAdd 1) by apply Fin.ext;rfl]
  simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
theorem erased_field (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (j : Fin 4) :
    erased cap fields source flag (field j)=fields j:=by
  rw [erased,install_other _ _ _ _ (by intro i;exact sweep_field j i)]
  simp only [input,field,Fin.addCases_right]
theorem erased_driver (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) :
    erased cap fields source flag 749=List.replicate cap true:=by
  rw [show (749 : Fin 759)=sweepSlot ((0 : Fin 2).natAdd 750) by decide,erased,install_slot _ sweep_injective]
  rfl
theorem erased_log (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) :
    erased cap fields source flag 750=List.replicate (cap+1) false:=by
  rw [show (750 : Fin 759)=sweepSlot ((1 : Fin 2).natAdd 750) by decide,erased,install_slot _ sweep_injective]
  rw [show ((1 : Fin 2).natAdd 750)=((0 : Fin 1).natAdd 751) by decide]
  simp only [PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self]
theorem bank_common (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ) (j : Fin 4) :
    bank cap fields source flag k (common j)=
      if j.val<k then ZeroPadding.pad cap (fields j) else List.replicate cap false:=
  install_slot _ common_injective _ _ _
theorem bank_other (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ)
    (i : Fin 759) (hi : ∀ j,common j≠i) :
    bank cap fields source flag k i=erased cap fields source flag i:=install_other _ _ _ _ hi
theorem bank_zero (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) :
    bank cap fields source flag 0=erased cap fields source flag:=by
  apply HierarchyAllocation.install_eq _ common_injective
  · intro j
    simp only [Nat.not_lt_zero,if_false]
    exact erased_common cap fields source flag j
  · intro i _
    rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBank

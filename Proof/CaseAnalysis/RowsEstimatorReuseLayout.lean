import Proof.CaseAnalysis.RowsEstimatorReset
import Proof.CaseAnalysis.RowsEstimatorAppendPadded

/-! One reusable estimator bank, with native source/C protected, an external
growing scalar stream, and a separately paid D driver and reset log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program):=WholePrefix.tapes p+1+2
def old (p : Program) (i : Fin (WholePrefix.tapes p)) : Fin (tapes p):=(i.castAdd 1).castAdd 2
def log (p : Program) : Fin (tapes p):=((0 : Fin 1).natAdd (WholePrefix.tapes p)).castAdd 2
def output (p : Program) : Fin (tapes p):=(0 : Fin 2).natAdd (WholePrefix.tapes p+1)
def driver (p : Program) : Fin (tapes p):=(1 : Fin 2).natAdd (WholePrefix.tapes p+1)
def native (p : Program) : Fin (tapes p):=old p ((52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p))
def capacity (p : Program) : Fin (tapes p):=old p (Retained.capacity p)
def copySlots (p : Program) : Fin 3→Fin (tapes p):=![old p (Whole.recordSlot p),output p,log p]

theorem copy_injective (p : Program) : Function.Injective (copySlots p):=by
  intro i j he
  have ht: (Whole.recordSlot p).val<WholePrefix.tapes p:=(Whole.recordSlot p).isLt
  fin_cases i <;>fin_cases j <;>first | rfl | (have hv:=congrArg Fin.val he;simp [copySlots,old,output,log] at hv <;>omega)

def work (p : Program) (i : Fin (WholePrefix.tapes p-2)) : Fin (tapes p):=
  if i.val<52 then ⟨i.val,by unfold tapes WholePrefix.tapes;omega⟩
  else if i.val<67 then ⟨i.val+1,by unfold tapes WholePrefix.tapes;omega⟩
  else ⟨i.val+2,by have h:=i.isLt;unfold tapes WholePrefix.tapes at *;omega⟩
theorem work_val (p : Program) (i : Fin (WholePrefix.tapes p-2)) :
    (work p i).val=if i.val<52 then i.val else if i.val<67 then i.val+1 else i.val+2:=by
  unfold work;split_ifs <;>rfl
theorem work_injective (p : Program) : Function.Injective (work p):=by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [work_val,work_val] at hv
  apply Fin.ext
  split_ifs at hv <;>omega
theorem work_bounds (p : Program) (i : Fin (WholePrefix.tapes p-2)) :
    (work p i).val<WholePrefix.tapes p ∧ (work p i).val≠52 ∧ (work p i).val≠68:=by
  have h:=i.isLt
  have ht:70≤WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
  rw [work_val]
  split_ifs <;>omega

def eraseSlots (p : Program) : Fin (WholePrefix.tapes p-2+1+1)→Fin (tapes p):=
  Fin.addCases (Fin.addCases (work p) (fun _ : Fin 1=>driver p)) (fun _ : Fin 1=>log p)
theorem erase_work (p : Program) (i : Fin (WholePrefix.tapes p-2)) :
    eraseSlots p ((i.castAdd 1).castAdd 1)=work p i:=by
  simp only [eraseSlots,Fin.addCases_left]
theorem erase_injective (p : Program) : Function.Injective (eraseSlots p):=by
  intro i j he
  revert he
  refine Fin.addCases (fun a=>?_) (fun a=>?_) i <;>refine Fin.addCases (fun b=>?_) (fun b=>?_) j
  · refine Fin.addCases (fun a=>?_) (fun a=>?_) a <;>refine Fin.addCases (fun b=>?_) (fun b=>?_) b
    · intro he
      rw [erase_work,erase_work] at he
      exact congrArg (fun k=>(k.castAdd 1).castAdd 1) (work_injective p he)
    · intro he
      have hv:=congrArg Fin.val he
      have hw:=work_bounds p a
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,driver,Fin.val_natAdd] at hv
      omega
    · intro he
      have hv:=congrArg Fin.val he
      have hw:=work_bounds p b
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,driver,Fin.val_natAdd] at hv
      omega
    · intro _
      rw [Subsingleton.elim a b]
  · intro he
    have hv:=congrArg Fin.val he
    revert hv
    refine Fin.addCases (fun k hk=>?_) (fun k hk=>?_) a
    · have hw:=work_bounds p k
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,log,Fin.val_castAdd,Fin.val_natAdd] at hk
      omega
    · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,log,driver,Fin.val_castAdd,Fin.val_natAdd] at hk
      omega
  · intro he
    have hv:=congrArg Fin.val he
    revert hv
    refine Fin.addCases (fun k hk=>?_) (fun k hk=>?_) b
    · have hw:=work_bounds p k
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,log,Fin.val_castAdd,Fin.val_natAdd] at hk
      omega
    · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,log,driver,Fin.val_castAdd,Fin.val_natAdd] at hk
      omega
  · intro _
    rw [Subsingleton.elim a b]

noncomputable def erase (p : Program):=RecoveryFocus.machine (eraseSlots p)
  (RecoveryScratchErase.resetMachine (WholePrefix.tapes p-2))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse

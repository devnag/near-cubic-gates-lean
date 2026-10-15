import Proof.CaseAnalysis.RowsBankCapacity

/-! Between polynomial families, the exact 0/1 head pattern permits one
left step and the existing C sweep. The accumulated output is never scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsBankFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroHeads (out : List Bool) (i : Fin 113) := if i=31 then out.length else 0
def position (forward : Bool) : Machine 113 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if raised i then if forward then .right else .left else .stay⟩ else none

theorem position_run (forward : Bool) (out : List Bool) (data : Fin 113→List Bool) :
    ∃ r,runFrom (position forward) 1
      ⟨0,if forward then zeroHeads out else heads out,data⟩=some r ∧
      r.final=⟨1,if forward then heads out else zeroHeads out,data⟩ ∧ r.steps=1 := by
  apply Timed.run (hd:=by rfl)
  apply Timed.single (by rfl)
  simp only [step,position,Fin.isValue,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    cases forward <;> fin_cases i <;> rfl
  · funext i
    rfl

def work (i : Fin 110) : Fin 113 :=
  if i.val<31 then ⟨i.val,by omega⟩ else if i.val<103 then ⟨i.val+1,by omega⟩
  else ⟨i.val+3,by have h:=i.isLt; omega⟩
theorem work_val (i : Fin 110) : (work i).val=if i.val<31 then i.val else if i.val<103 then i.val+1 else i.val+3 := by
  unfold work
  split_ifs <;> rfl
theorem work_injective : Function.Injective work := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  rw [work_val,work_val] at hv
  split_ifs at hv <;> omega
theorem work_avoids (i : Fin 110) : work i≠31 ∧ work i≠104 ∧ work i≠105 := by
  have hv:=work_val i
  constructor
  · intro he; have h:=congrArg Fin.val he; rw [hv] at h; split_ifs at h <;> omega
  constructor
  · intro he; have h:=congrArg Fin.val he; rw [hv] at h; split_ifs at h <;> omega
  · intro he; have h:=congrArg Fin.val he; rw [hv] at h; split_ifs at h <;> omega

def slots : Fin 112→Fin 113 := Fin.addCases (m:=110) (n:=2) work ![104,105]
theorem slots_injective : Function.Injective slots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=110) (n:=2) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=110) (n:=2) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [slots,Fin.addCases_left] at he
    exact congrArg (fun k : Fin 110=>k.castAdd 2) (work_injective he)
  · intro he
    simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
    fin_cases b
    · exact False.elim ((work_avoids a).2.1 he)
    · exact False.elim ((work_avoids a).2.2 he)
  · intro he
    simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
    fin_cases a
    · exact False.elim ((work_avoids b).2.1 he.symm)
    · exact False.elim ((work_avoids b).2.2 he.symm)
  · intro he
    fin_cases a <;> fin_cases b <;> first | rfl | contradiction
theorem slots_avoid (i : Fin 112) : slots i≠31 := by
  refine Fin.addCases (m:=110) (n:=2) (fun a=>?_) (fun a=>?_) i
  · simpa only [slots,Fin.addCases_left] using (work_avoids a).1
  · fin_cases a <;> decide

noncomputable def erase := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 110)
noncomputable def machine := Composition.machine (position false) erase
def budget (C : ℕ) := 2*C+6
def erased (C : ℕ) : Fin 112→List Bool :=
  Fin.addCases (m:=111) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=110) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>List.replicate C false) (fun _=>List.replicate C true)) (fun _=>List.replicate (C+1) false)
theorem slots_work (i : Fin 110) : slots ((i.castAdd 1).castAdd 1)=work i := by
  change slots (i.castAdd 2)=work i
  simp only [slots,Fin.addCases_left]
def blank (C : ℕ) (out : List Bool) (i : Fin 113) :=
  if i=31 then out else if i=104 then List.replicate C true
  else if i=105 then List.replicate (C+1) false else List.replicate C false

theorem clear_run (C : ℕ) (out : List Bool) (data : Fin 113→List Bool)
    (hsize : ∀ i,i≠31 → i≠105 → (data i).length ≤ C)
    (hd : data 104=List.replicate C true) (hl : data 105=List.replicate (C+1) false) :
    ∃ r,runFrom machine (budget C) ⟨machine.start,heads out,data⟩=some r ∧
      r.final.heads=zeroHeads out ∧
      (∀ i,r.final.tapes (slots i)=erased C i) ∧
      r.final.tapes 31=data 31 ∧ r.steps ≤ budget C := by
  obtain ⟨a,ha,af,_⟩ := position_run false out data
  have base := RecoveryScratchErase.erase_ready C (C+1) (fun i=>data (work i))
    (fun i=>hsize (work i) (work_avoids i).1 (work_avoids i).2.2)
  obtain ⟨b,hb,bh,bt,_⟩ := base.focus_at slots slots_injective (zeroHeads out) data
    (by
      intro i
      refine Fin.addCases (m:=111) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=110) (n:=1) (fun k=>?_) (fun k=>?_) j
        · simp only [slots_work,Fin.addCases_left]
        · fin_cases k
          exact hd
      · fin_cases j
        exact hl)
    (by intro i; simp only [zeroHeads,slots_avoid i,↓reduceIte])
  have he : Composition.restart a.final erase.start=⟨erase.start,zeroHeads out,data⟩ := by rw [af]; rfl
  change runFrom erase (2*C+4) ⟨erase.start,zeroHeads out,data⟩=some b at hb
  rw [←he] at hb
  have whole := Composition.run_join (position false) erase _ _ _ a b ha hb
  have hfuel : 1+1+(2*C+4)=budget C := by unfold budget; omega
  rw [hfuel] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · intro i
    change b.final.tapes (slots i)=_
    rw [bt,install_slot _ slots_injective]
    simp only [erased,Nat.max_self]
  · change b.final.tapes 31=data 31
    rw [bt,install_other _ _ _ _ slots_avoid]

end NearCubicWires.RepairOrdinary.CloseoutRowsBankClear

import Proof.CaseAnalysis.RecoveryRowCollect

/-! One charged sweep clears the complete row work bank. The original
graph/count/literal source and the saved outer row stack are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowErase
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def work (i : Fin 70) : Fin 78:=
  if i.val<20 then ⟨i.val,by omega⟩ else if i.val<24 then ⟨i.val+1,by omega⟩
  else if i.val<68 then ⟨i.val+2,by omega⟩ else ⟨i.val+3,by have h:=i.isLt;omega⟩
theorem work_val (i : Fin 70) : (work i).val=
    if i.val<20 then i.val else if i.val<24 then i.val+1 else if i.val<68 then i.val+2 else i.val+3 := by
  unfold work
  split_ifs <;> rfl
theorem work_injective : Function.Injective work := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  rw [work_val,work_val] at hv
  split_ifs at hv <;> omega
theorem work_spec (i : Fin 70) : (work i).val<73 ∧ work i≠20 ∧ work i≠25 ∧ work i≠70 := by
  have hv:=work_val i
  have hi:=i.isLt
  refine ⟨?_,?_,?_,?_⟩
  · rw [hv];split_ifs <;> omega
  · intro he;have h:=congrArg Fin.val he;rw [hv] at h;split_ifs at h <;> omega
  · intro he;have h:=congrArg Fin.val he;rw [hv] at h;split_ifs at h <;> omega
  · intro he;have h:=congrArg Fin.val he;rw [hv] at h;split_ifs at h <;> omega
theorem work_covers (i : Fin 78) (hi : i.val<73) (h20 : i≠20) (h25 : i≠25) (h70 : i≠70) :
    ∃ j,work j=i := by
  have n20 : i.val≠20:=fun h=>h20 (Fin.ext h)
  have n25 : i.val≠25:=fun h=>h25 (Fin.ext h)
  have n70 : i.val≠70:=fun h=>h70 (Fin.ext h)
  by_cases a : i.val<20
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext;rw [work_val];simp only [a,↓reduceIte]
  by_cases b : i.val<25
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext;rw [work_val];dsimp only;split_ifs <;> omega
  by_cases c : i.val<70
  · refine ⟨⟨i.val-2,by omega⟩,?_⟩
    apply Fin.ext;rw [work_val];dsimp only;split_ifs <;> omega
  · refine ⟨⟨i.val-3,by omega⟩,?_⟩
    apply Fin.ext;rw [work_val];dsimp only;split_ifs <;> omega

def slots : Fin 72→Fin 78:=Fin.addCases (m:=70) (n:=2) work ![76,77]
theorem work_high (i : Fin 70) (j : Fin 78) (hj : 73≤j.val) : work i≠j := by
  intro he
  have h:=congrArg Fin.val he
  have hw:=(work_spec i).1
  omega
theorem slots_injective : Function.Injective slots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=70) (n:=2) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=70) (n:=2) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [slots,Fin.addCases_left] at he
    exact congrArg (fun k : Fin 70=>k.castAdd 2) (work_injective he)
  · intro he
    simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
    fin_cases b
    · exact False.elim (work_high a 76 (by decide) he)
    · exact False.elim (work_high a 77 (by decide) he)
  · intro he
    simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
    fin_cases a
    · exact False.elim (work_high b 76 (by decide) he.symm)
    · exact False.elim (work_high b 77 (by decide) he.symm)
  · intro he
    fin_cases a <;> fin_cases b <;> first | rfl | contradiction
theorem slots_work (i : Fin 70) : slots ((i.castAdd 1).castAdd 1)=work i := by
  change slots (i.castAdd 2)=work i
  simp only [slots,Fin.addCases_left]

noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 70)
def data (B : ℕ) (A : Fin 78→List Bool) (i : Fin 78):=
  if i.val<73 ∧ i≠20 ∧ i≠25 ∧ i≠70 then List.replicate B false else A i

theorem erase_run (B : ℕ) (H : Fin 78→ℕ) (A : Fin 78→List Bool)
    (hH : ∀ i,H (slots i)=0) (hA : ∀ i,(A (work i)).length ≤ B)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false) :
    ∃ r,runFrom machine (2*B+4) ⟨machine.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=data B A ∧ r.steps ≤ 2*B+4 := by
  have base:=RecoveryScratchErase.erase_ready B (B+1) (fun i=>A (work i)) hA
  obtain ⟨r,rr,rh,rt,rs⟩:=base.focus_at slots slots_injective H A
    (by
      intro i
      refine Fin.addCases (m:=71) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=70) (n:=1) (fun k=>?_) (fun k=>?_) j
        · simp only [slots_work,Fin.addCases_left]
        · fin_cases k;exact hd
      · fin_cases j;exact hl) hH
  refine ⟨r,rr,rh,?_,rs.le⟩
  rw [rt]
  funext i
  by_cases hw : i.val<73 ∧ i≠20 ∧ i≠25 ∧ i≠70
  · obtain ⟨j,rfl⟩:=work_covers i hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
    rw [←slots_work,install_slot _ slots_injective]
    simp only [Fin.addCases_left,slots_work,data,if_pos (work_spec j)]
  · by_cases h76 : i=76
    · subst i
      change install slots A _ (slots ((0 : Fin 2).natAdd 70))=_
      rw [install_slot _ slots_injective]
      change List.replicate B true=data B A 76
      simpa only [data,hw,↓reduceIte] using hd.symm
    by_cases h77 : i=77
    · subst i
      change install slots A _ (slots ((1 : Fin 2).natAdd 70))=_
      rw [install_slot _ slots_injective]
      change List.replicate (max (B+1) (B+1)) false=data B A 77
      simpa only [data,hw,↓reduceIte,Nat.max_self] using hl.symm
    · rw [install_other _ _ _ _ (by
        intro j
        refine Fin.addCases (m:=70) (n:=2) (fun a=>?_) (fun a=>?_) j
        · intro he
          apply hw
          simp only [slots,Fin.addCases_left] at he
          rw [←he]
          exact work_spec a
        · fin_cases a
          · exact fun he=>h76 he.symm
          · exact fun he=>h77 he.symm)]
      exact (if_neg hw).symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowErase

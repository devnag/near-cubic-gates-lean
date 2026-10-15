import Proof.CaseAnalysis.WitnessTermBegin

/-! One successful circuit exit clears only the private circuit bank.
Its paid driver is separate from the circuit's internal capacity, so the
actual support bound, including retained erase logs, remains explicit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitReset
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateSlot (i : Fin 1697) : Fin 1703 :=
  ⟨if i.val<1 then i.val else if i.val<1673 then i.val+1 else
    if i.val<1686 then i.val+2 else if i.val<1691 then i.val+3 else
    if i.val<1694 then i.val+4 else i.val+6,by split_ifs <;> omega⟩
def retained (i : Fin 1703) : Prop :=
  i.val=1 ∨ i.val=1674 ∨ i.val=1688 ∨ i.val=1694 ∨ i.val=1698 ∨ i.val=1699
def scratch (i : Fin 1697) : Fin 2532 := ⟨827+(privateSlot i).val,by have h:=(privateSlot i).isLt;omega⟩
def slots (i : Fin 1699) : Fin 2532 :=
  if h : i.val<1697 then scratch ⟨i.val,h⟩ else ⟨i.val+833,by omega⟩

theorem slots_old (i : Fin 1697) : slots (i.castAdd 2)=scratch i := by
  simp only [slots,Fin.val_castAdd,dif_pos i.isLt]
theorem slots_new (i : Fin 2) : slots (i.natAdd 1697)=![2530,2531] i := by
  fin_cases i <;> rfl
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1697)

theorem private_injective : Function.Injective privateSlot := by
  intro i j h
  have hv := congrArg (fun k : Fin 1703=>k.val) h
  dsimp only [privateSlot] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem private_not_retained (i : Fin 1697) : ¬retained (privateSlot i) := by
  dsimp only [retained,privateSlot]
  split_ifs <;> omega

theorem slots_injective : Function.Injective slots := by
  intro i j h
  by_cases hi : i.val<1697
  · by_cases hj : j.val<1697
    · rw [slots,dif_pos hi,slots,dif_pos hj] at h
      have hv := congrArg (fun k : Fin 2532=>k.val) h
      change 827+(privateSlot ⟨i.val,hi⟩).val=827+(privateSlot ⟨j.val,hj⟩).val at hv
      have hp : privateSlot ⟨i.val,hi⟩=privateSlot ⟨j.val,hj⟩ := Fin.ext (by omega)
      exact Fin.ext (congrArg (fun z : Fin 1697=>z.val) (private_injective hp))
    · rw [slots,dif_pos hi,slots,dif_neg hj] at h
      have hv := congrArg (fun k : Fin 2532=>k.val) h
      have hp := (privateSlot ⟨i.val,hi⟩).isLt
      change 827+(privateSlot ⟨i.val,hi⟩).val=j.val+833 at hv
      omega
  · by_cases hj : j.val<1697
    · rw [slots,dif_neg hi,slots,dif_pos hj] at h
      have hv := congrArg (fun k : Fin 2532=>k.val) h
      have hp := (privateSlot ⟨j.val,hj⟩).isLt
      change i.val+833=827+(privateSlot ⟨j.val,hj⟩).val at hv
      omega
    · rw [slots,dif_neg hi,slots,dif_neg hj] at h
      have hv := congrArg (fun k : Fin 2532=>k.val) h
      exact Fin.ext (by change i.val+833=j.val+833 at hv;omega)

theorem term_outside (i : Fin 827) : ∀ j,slots j≠i.castAdd 1705 := by
  intro j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  by_cases hj : j.val<1697
  · rw [slots,dif_pos hj] at hv
    change 827+(privateSlot ⟨j.val,hj⟩).val=i.val at hv
    omega
  · rw [slots,dif_neg hj] at hv
    change j.val+833=i.val at hv
    omega

theorem retained_outside (i : Fin 1703) (hi : retained i) :
    ∀ j,slots j≠(⟨827+i.val,by omega⟩ : Fin 2532) := by
  intro j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  by_cases hj : j.val<1697
  · rw [slots,dif_pos hj] at hv
    change 827+(privateSlot ⟨j.val,hj⟩).val=827+i.val at hv
    have he : privateSlot ⟨j.val,hj⟩=i := Fin.ext (by omega)
    exact private_not_retained ⟨j.val,hj⟩ (he ▸ hi)
  · rw [slots,dif_neg hj] at hv
    change j.val+833=827+i.val at hv
    omega

private theorem erase_at {t k : ℕ} (slot : Fin (k+1+1) → Fin t)
    (inj : Function.Injective slot) (H : ℕ) (heads : Fin t → ℕ) (input : Fin t → List Bool)
    (hh : ∀ i,heads (slot i)=0)
    (hd : input (slot ((0 : Fin 1).natAdd k |>.castAdd 1))=List.replicate H true)
    (hl : input (slot ((0 : Fin 1).natAdd (k+1)))=List.replicate (H+1) false)
    (hb : ∀ i : Fin k,(input (slot ((i.castAdd 1).castAdd 1))).length ≤ H) :
    ∃ result,runFrom (RecoveryFocus.machine slot (RecoveryScratchErase.resetMachine k)) (2*H+4)
        ⟨(RecoveryFocus.machine slot (RecoveryScratchErase.resetMachine k)).start,heads,input⟩=some result ∧
      result.steps ≤ 2*H+4 ∧ result.final.heads=heads ∧
      result.final.tapes=install slot input (PCPTraversal.clearedLocal k H (H+1)) := by
  let backing := fun i : Fin k=>input (slot ((i.castAdd 1).castAdd 1))
  obtain ⟨r,hr,rh,rt,rs⟩ := (RecoveryScratchErase.erase_ready H (H+1) backing hb).focus_at
    slot inj heads input (by
      intro i
      refine Fin.addCases (m:=k+1) (n:=1) ?_ ?_ i
      · intro j
        refine Fin.addCases (m:=k) (n:=1) ?_ ?_ j
        · intro z;simp only [Fin.addCases_left,backing]
        · intro z;have hz : z=0 := Fin.eq_zero z;subst z
          simpa only [Fin.addCases_left,Fin.addCases_right] using hd
      · intro z;have hz : z=0 := Fin.eq_zero z;subst z
        simpa only [Fin.addCases_right] using hl) hh
  exact ⟨r,hr,rs.le,rh,rt⟩

theorem reset_run (H : ℕ) (heads : Fin 2532 → ℕ) (input : Fin 2532 → List Bool)
    (hh : ∀ i,heads (slots i)=0)
    (hd : input 2530=List.replicate H true)
    (hl : input 2531=List.replicate (H+1) false)
    (hb : ∀ i,(input (scratch i)).length ≤ H) :
    ∃ result,runFrom machine (2*H+4) ⟨machine.start,heads,input⟩=some result ∧
      result.steps ≤ 2*H+4 ∧ result.final.heads=heads ∧
      (∀ i,result.final.tapes (scratch i)=List.replicate H false) ∧
      result.final.tapes 2530=List.replicate H true ∧
      result.final.tapes 2531=List.replicate (H+1) false ∧
      (∀ i,(∀ j,slots j≠i) → result.final.tapes i=input i) := by
  obtain ⟨r,hr,rs,rh,rt⟩ := erase_at slots slots_injective H heads input hh hd hl (by
    intro i
    have he : (i.castAdd 1).castAdd 1=i.castAdd 2 := Fin.ext rfl
    rw [he,slots_old]
    exact hb i)
  refine ⟨r,hr,rs,rh,?_,?_,?_,?_⟩
  · intro i
    rw [rt]
    have h := install_slot slots slots_injective input (PCPTraversal.clearedLocal 1697 H (H+1)) (i.castAdd 2)
    rw [slots_old] at h
    have he : i.castAdd 2=(i.castAdd 1).castAdd 1 := Fin.ext rfl
    rw [he] at h
    simpa only [PCPTraversal.clearedLocal,Fin.addCases_left] using h
  · rw [rt]
    exact install_slot slots slots_injective input _ 1697
  · rw [rt]
    have h := install_slot slots slots_injective input (PCPTraversal.clearedLocal 1697 H (H+1))
      ((0 : Fin 1).natAdd 1698)
    change install slots input _ 2531=PCPTraversal.clearedLocal 1697 H (H+1) ((0 : Fin 1).natAdd 1698) at h
    simpa only [PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self] using h
  · intro i hi;rw [rt];exact install_other _ _ _ _ hi

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitReset

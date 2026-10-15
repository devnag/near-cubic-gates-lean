import Proof.CaseAnalysis.WitnessSumDock

/-! A successful sum clears its one private header/count bank with the
already paid H driver. The source arity, term cap, verdict and native
count stream survive. No failed branch enters this reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumReset
open LocalBitMultitape RecoveryRootRound
open private erase_at from Proof.CaseAnalysis.WitnessTermCircuitReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateSlot (i : Fin 524) : Fin 528 :=
  ⟨if i.val<499 then i.val else if i.val=499 then 500 else if i.val<523 then i.val+3 else 527,
    by split_ifs <;> omega⟩
def retained (i : Fin 528) : Prop := i.val=499 ∨ i.val=501 ∨ i.val=502 ∨ i.val=526
def scratch (i : Fin 524) := SumDock.slots (privateSlot i)
def slots : Fin 526 → Fin 3061 :=
  Fin.addCases (m:=524) (n:=2) (motive:=fun _=>Fin 3061) scratch ![2530,2531]
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 524)

theorem private_injective : Function.Injective privateSlot := by
  intro i j h
  have hv := congrArg (fun k : Fin 528=>k.val) h
  dsimp only [privateSlot] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem private_not_retained (i : Fin 524) : ¬retained (privateSlot i) := by
  dsimp only [retained,privateSlot]
  split_ifs <;> omega

theorem private_covers (i : Fin 528) (hi : ¬retained i) : ∃ j,privateSlot j=i := by
  have hn : i.val≠499 ∧ i.val≠501 ∧ i.val≠502 ∧ i.val≠526 := by
    simpa only [retained,not_or] using hi
  let j : Fin 524:=⟨if i.val<499 then i.val else if i.val=500 then 499 else if i.val<526 then i.val-3 else 523,
    by split_ifs <;> omega⟩
  refine ⟨j,Fin.ext ?_⟩
  dsimp only [privateSlot,j]
  split_ifs <;> omega

theorem sum_outside (i : Fin 528) : SumDock.slots i≠2530 ∧ SumDock.slots i≠2531 := by
  constructor <;> intro h <;> have hv := congrArg (fun k : Fin 3061=>k.val) h
  all_goals dsimp only [SumDock.slots] at hv;split_ifs at hv <;> omega

theorem slots_injective : Function.Injective slots := by
  intro i j
  refine Fin.addCases (m:=524) (n:=2) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=524) (n:=2) (fun j=>?_) (fun j=>?_) j
    · intro h
      simp only [slots,Fin.addCases_left,scratch] at h
      exact congrArg (Fin.castAdd 2) (private_injective (SumDock.slots_injective h))
    · intro h
      simp only [slots,Fin.addCases_left,Fin.addCases_right,scratch] at h
      fin_cases j
      · exact ((sum_outside (privateSlot i)).1 h).elim
      · exact ((sum_outside (privateSlot i)).2 h).elim
  · refine Fin.addCases (m:=524) (n:=2) (fun j=>?_) (fun j=>?_) j
    · intro h
      simp only [slots,Fin.addCases_left,Fin.addCases_right,scratch] at h
      fin_cases i
      · exact ((sum_outside (privateSlot j)).1 h.symm).elim
      · exact ((sum_outside (privateSlot j)).2 h.symm).elim
    · intro h
      fin_cases i <;> fin_cases j <;> first | rfl | (have hv:=congrArg (fun k : Fin 3061=>k.val) h;cases hv)

theorem reset_run (H : ℕ) (heads : Fin 3061 → ℕ) (input : Fin 3061 → List Bool)
    (hh : ∀ i,heads (slots i)=0) (hd : input 2530=List.replicate H true)
    (hl : input 2531=List.replicate (H+1) false)
    (hb : ∀ i,(input (scratch i)).length ≤ H) :
    ∃ r,runFrom machine (2*H+4) ⟨machine.start,heads,input⟩=some r ∧
      r.steps ≤ 2*H+4 ∧ r.final.heads=heads ∧
      (∀ i,r.final.tapes (scratch i)=List.replicate H false) ∧
      r.final.tapes 2530=List.replicate H true ∧ r.final.tapes 2531=List.replicate (H+1) false ∧
      (∀ i,(∀ j,slots j≠i) → r.final.tapes i=input i) := by
  obtain ⟨r,run,rs,rh,rt⟩ := erase_at slots slots_injective H heads input hh hd hl (by
    intro i
    have he : (i.castAdd 1).castAdd 1=i.castAdd 2 := Fin.ext rfl
    rw [he,slots,Fin.addCases_left]
    exact hb i)
  refine ⟨r,run,rs,rh,?_,?_,?_,?_⟩
  · intro i
    rw [rt]
    have h := install_slot slots slots_injective input (PCPTraversal.clearedLocal 524 H (H+1)) (i.castAdd 2)
    have he : i.castAdd 2=(i.castAdd 1).castAdd 1 := Fin.ext rfl
    rw [show slots (i.castAdd 2)=scratch i by simp only [slots,Fin.addCases_left]] at h
    rw [he] at h
    simpa only [PCPTraversal.clearedLocal,Fin.addCases_left] using h
  · rw [rt]
    exact install_slot slots slots_injective input _ 524
  · rw [rt]
    have h := install_slot slots slots_injective input (PCPTraversal.clearedLocal 524 H (H+1)) (525 : Fin 526)
    change install slots input _ 2531=PCPTraversal.clearedLocal 524 H (H+1) ((0 : Fin 1).natAdd 525) at h
    simpa only [PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self] using h
  · intro i hi;rw [rt];exact install_other _ _ _ _ hi

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumReset

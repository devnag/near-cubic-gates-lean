import Proof.CaseAnalysis.RecoverySelectorLoopLayout

/-! Concrete bank projections used by the repeated original-selector body. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem guard_pick (i : Fin 37) :
    RecoveryFocus.pick RecoveryBoundedNativeGuarded.slots i=
      if i=36 then some 1 else if h : i.val<29 ∧ i.val≠1 then some ⟨i.val,h.1⟩ else none := by
  by_cases hi : i=36
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective 1
  rw [if_neg hi]
  split_ifs with h
  · let j : Fin 29:=⟨i.val,h.1⟩
    have hj : j≠1 := fun he=>h.2 (congrArg Fin.val he)
    have he : RecoveryBoundedNativeGuarded.slots j=i := by
      rw [RecoveryBoundedNativeGuarded.slots,if_neg hj]
      exact Fin.ext rfl
    conv_lhs=>rw [←he]
    exact RecoveryFocus.pick_slot RecoveryBoundedNativeGuarded.slots RecoveryBoundedNativeGuarded.slots_injective j
  · have hn : ¬∃ j,RecoveryBoundedNativeGuarded.slots j=i := by
      rintro ⟨j,hj⟩
      by_cases h1 : j=1
      · subst j
        exact hi hj.symm
      · have hv:=congrArg Fin.val hj
        simp only [RecoveryBoundedNativeGuarded.slots,if_neg h1,Fin.val_castAdd] at hv
        have hne : j.val≠1 := fun he=>h1 (Fin.ext he)
        exact h ⟨hv ▸ j.isLt,by omega⟩
    simp only [RecoveryFocus.pick,dif_neg hn]

@[simp] theorem fold_pick (i : Fin 36) :
    RecoveryFocus.pick RecoveryBoundedNativeUnaryJoin.foldSlots i=
      if i=34 then none else if h : i.val<34 then some ((⟨i.val,h⟩ : Fin 34).castAdd 1) else some 34 := by
  by_cases hi : i=34
  · subst i
    have hn : ¬∃ j,RecoveryBoundedNativeUnaryJoin.foldSlots j=34 := by decide
    rw [if_pos rfl]
    simp only [RecoveryFocus.pick,dif_neg hn]
  rw [if_neg hi]
  split_ifs with h
  · let j : Fin 34:=⟨i.val,h⟩
    have he : RecoveryBoundedNativeUnaryJoin.foldSlots (j.castAdd 1)=i := by
      simp only [RecoveryBoundedNativeUnaryJoin.foldSlots,Fin.addCases_left]
      exact Fin.ext rfl
    conv_lhs=>rw [←he]
    exact RecoveryFocus.pick_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide) (j.castAdd 1)
  · have hv : i.val=35 := by
      have hb:=i.isLt
      have hne : i.val≠34 := fun he=>hi (Fin.ext he)
      omega
    have he : i=35 := Fin.ext hv
    subst i
    exact RecoveryFocus.pick_slot RecoveryBoundedNativeUnaryJoin.foldSlots (by decide) 34

@[simp] theorem join_pick (i : Fin 41) :
    RecoveryFocus.pick RecoveryBoundedSelectorJoin.slots i=
      if i=25 then some 0 else if i=40 then some 1 else if i=32 then some 2 else none := by
  by_cases h0 : i=25
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot RecoveryBoundedSelectorJoin.slots (by decide) 0
  rw [if_neg h0]
  by_cases h1 : i=40
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot RecoveryBoundedSelectorJoin.slots (by decide) 1
  rw [if_neg h1]
  by_cases h2 : i=32
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot RecoveryBoundedSelectorJoin.slots (by decide) 2
  rw [if_neg h2]
  have hn : ¬∃ j,RecoveryBoundedSelectorJoin.slots j=i := by
    rintro ⟨j,hj⟩
    fin_cases j
    · exact h0 hj.symm
    · exact h1 hj.symm
    · exact h2 hj.symm
  simp only [RecoveryFocus.pick,dif_neg hn]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop

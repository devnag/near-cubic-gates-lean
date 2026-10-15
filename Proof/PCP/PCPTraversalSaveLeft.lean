import Proof.PCP.PCPTraversalReturn

/-! Executed saving of the canonical left-child result, nodes10→12. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def saveLeftSlots : Fin 3 → Fin 128 := ![77,82,92]
theorem saveLeftSlots_injective : Function.Injective saveLeftSlots := by decide
def saveLeftInput (bits stack : List Bool) (cap stackCap : ℕ) : Configuration 3 4 :=
  ⟨PCPStackPush.machine.start,![0,stack.length,0],
    ![ZeroPadding.pad cap (frame bits),ZeroPadding.pad stackCap stack,List.replicate cap false]⟩
def saveLeftLocal (bits stack : List Bool) (cap stackCap : ℕ) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (frame bits),ZeroPadding.pad stackCap (stack++(frame bits).reverse),
    List.replicate cap false]
def saveLeftHeads (bits stack : List Bool) : Fin 3 → ℕ := ![0,stack.length+2*bits.length+1,0]
noncomputable def leftSaved (bits stack : List Bool) (cap stackCap log : ℕ)
    (ambient : Fin 128 → List Bool) :=
  install saveLeftSlots (cleared rightPushClearSlots cap log ambient) (saveLeftLocal bits stack cap stackCap)

theorem padded_save_left_run (bits stack : List Bool) (cap stackCap : ℕ)
    (hc : 2*bits.length+1≤cap) :
    ∃ r,runFrom PCPStackPush.machine (4*bits.length+3) (saveLeftInput bits stack cap stackCap)=some r ∧
      r.final.tapes=saveLeftLocal bits stack cap stackCap ∧
      r.final.heads=saveLeftHeads bits stack ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs⟩ := PCPStackReady.push_run bits stack stackCap cap
  let caps : Fin 3 → ℕ := ![cap,0,0]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config PCPStackPush.machine caps _ _ base hr
  have he : ZeroPadding.config caps (PCPStackReady.pushInput bits stack stackCap cap)=
      saveLeftInput bits stack cap stackCap := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i
      · rfl
      · exact ZeroPadding.pad_zero _
      · exact ZeroPadding.pad_zero _
  rw [he] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hfinal,hf]
    funext i; fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad 0 (List.replicate (max cap (2*bits.length+1)) false)=List.replicate cap false
      rw [ZeroPadding.pad_zero,max_eq_left hc]
  · rw [hfinal,hf]
    funext i; fin_cases i
    · rfl
    · change (stack++(frame bits).reverse).length=stack.length+2*bits.length+1
      simp [frame_length]; omega
    · rfl

theorem save_left_path (bits stack : List Bool) (cap stackCap log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 2*bits.length+1≤cap) (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hsource : ambient 77=ZeroPadding.pad cap (frame bits))
    (hstack : ambient 82=ZeroPadding.pad stackCap stack)
    (hstackHead : heads 82=stack.length) (hhd : heads 28=0) :
    Path 10 12 (2*cap+4*bits.length+9) heads ambient
      (installedHeads saveLeftSlots heads (saveLeftHeads bits stack))
      (leftSaved bits stack cap stackCap log ambient) := by
  have hclear := clear_path 10 11 rightPushClearSlots rfl (by intro q scanned; simp [next])
    rightPushClearSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i; exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i; exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨base,hr,ht,hheads,_⟩ := padded_save_left_run bits stack cap stackCap hc
  obtain ⟨r,hrun,_,hrh,hrt,_⟩ := focused_run_at PCPStackPush.machine saveLeftSlots saveLeftSlots_injective
    heads (cleared rightPushClearSlots cap log ambient) _ base hr rfl
    (by intro i; fin_cases i
        · exact hh _ (by decide) (by decide) (by decide) (by decide)
        · exact hstackHead
        · exact hh _ (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i
        · exact (cleared_other rightPushClearSlots cap log ambient 77 (by decide) (by decide) (by decide)).trans hsource
        · exact (cleared_other rightPushClearSlots cap log ambient 82 (by decide) (by decide) (by decide)).trans hstack
        · exact cleared_slot rightPushClearSlots rightPushClearSlots_injective (by decide) (by decide) cap log ambient 0)
  rw [hheads] at hrh
  rw [ht] at hrt
  have hsave := packed_moving_path 11 12 (focused saveLeftSlots PCPStackPush.machine) rfl
    (4*bits.length+3) heads _ (cleared rightPushClearSlots cap log ambient) _ ⟨r,hrun,hrh,hrt⟩
    (by intro q scanned; simp [next])
  have hpath := hclear.trans hsave
  have he : (2*cap+5)+(4*bits.length+3+1)=2*cap+4*bits.length+9 := by omega
  rw [he] at hpath
  exact hpath

theorem WorkBound.leftSaved {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (bits stack : List Bool) (stackCap : ℕ)
    (hstackCap : stackCap≤cap) (hfit : stack.length+2*bits.length+1≤cap) :
    WorkBound cap (leftSaved bits stack cap stackCap log ambient) := by
  apply (hb.clear rightPushClearSlots rightPushClearSlots_injective (by decide) (by decide)).install saveLeftSlots
  intro i _ _
  fin_cases i
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl (by omega)
  · change (ZeroPadding.pad stackCap (stack++(frame bits).reverse)).length≤cap
    rw [ZeroPadding.pad_length,List.length_append,List.length_reverse,frame_length]
    exact max_le hstackCap (by omega)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

theorem WorkingHeads.leftSaved {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (bits stack : List Bool) : WorkingHeads (installedHeads saveLeftSlots heads (saveLeftHeads bits stack)) := by
  apply hh.install saveLeftSlots
  intro i _ _ _ h82
  fin_cases i
  · rfl
  · exact False.elim (h82 rfl)
  · rfl

end NearCubicWires.RepairOrdinary.PCPTraversal

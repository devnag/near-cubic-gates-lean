import Proof.PCP.PCPTraversalSaveLeft

/-! Controller12→0 physically pops the pending right-child count and
reconstructs its raw unary driver after sweeping all four local work tapes. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rightPopClearSlots : Fin 4 → Fin 128 := ![93,94,79,95]
def rightPopSlots : Fin 5 → Fin 128 := ![80,93,94,79,95]
theorem rightPopClearSlots_injective : Function.Injective rightPopClearSlots := by decide
theorem rightPopSlots_injective : Function.Injective rightPopSlots := by decide
noncomputable def rightPopInput (n cap z : ℕ) (pre : List Bool) : Configuration 5 11 :=
  ⟨PCPUnaryStackPop.machine.start,![pre.length+2*n+1,0,0,0,0],
    ![pre++(frame (List.replicate n true)).reverse++List.replicate z false,
      List.replicate cap false,List.replicate cap false,List.replicate cap false,List.replicate cap false]⟩
def rightPopLocal (n cap z : ℕ) (pre : List Bool) : Fin 5 → List Bool :=
  ![pre++List.replicate (2*n+1+z) false,ZeroPadding.pad cap (frame (List.replicate n true)),
    List.replicate cap false,ZeroPadding.pad cap (List.replicate n true),List.replicate cap false]
noncomputable def rightPopped (n cap z log : ℕ) (pre : List Bool)
    (ambient : Fin 128 → List Bool) :=
  install rightPopSlots (cleared rightPopClearSlots cap log ambient) (rightPopLocal n cap z pre)

theorem padded_right_pop_run (n cap z : ℕ) (pre : List Bool) (hc : 2*n+2≤cap) :
    ∃ r,runFrom PCPUnaryStackPop.machine (8*n+9) (rightPopInput n cap z pre)=some r ∧
      r.final.tapes=rightPopLocal n cap z pre ∧
      r.final.heads=PCPUnaryStackPop.heads pre ∧ r.steps=8*n+9 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := PCPUnaryStackPop.pop_run n pre z
  let caps : Fin 5 → ℕ := ![0,cap,cap,cap,cap]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config PCPUnaryStackPop.machine caps _ _ base hr
  have he : ZeroPadding.config caps (PCPUnaryStackPop.entry n pre z)=rightPopInput n cap z pre := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i
      · change pre.length+(frame (List.replicate n true)).length=pre.length+2*n+1
        rw [frame_length,List.length_replicate]
        omega
      · rfl
      · rfl
      · rfl
      · rfl
    · funext i; fin_cases i
      · exact ZeroPadding.pad_zero _
      · rfl
      · rfl
      · rfl
      · rfl
  rw [he] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hfinal]
    change (fun i => ZeroPadding.pad (caps i) (base.final.tapes i))=_
    rw [ht]
    funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad cap (List.replicate (2*n+2) false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
    · rfl
    · change ZeroPadding.pad cap (List.replicate n false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · rw [hfinal]
    exact hh

theorem right_pop_path (n cap z log : ℕ) (pre : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 2*n+2≤cap) (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hstack : ambient 80=pre++(frame (List.replicate n true)).reverse++List.replicate z false)
    (hstackHead : heads 80=pre.length+2*n+1) (hhd : heads 28=0) :
    Path 12 0 (2*cap+8*n+15) heads ambient
      (installedHeads rightPopSlots heads (PCPUnaryStackPop.heads pre))
      (rightPopped n cap z log pre ambient) := by
  have hclear := clear_path 12 13 rightPopClearSlots rfl (by intro q scanned; simp [next])
    rightPopClearSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i <;> exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨base,hr,ht,hheads,_⟩ := padded_right_pop_run n cap z pre hc
  obtain ⟨r,hrun,_,hrh,hrt,_⟩ := focused_run_at PCPUnaryStackPop.machine rightPopSlots rightPopSlots_injective
    heads (cleared rightPopClearSlots cap log ambient) _ base hr rfl
    (by intro i; fin_cases i
        · exact hstackHead
        · exact hh _ (by decide) (by decide) (by decide) (by decide)
        · exact hh _ (by decide) (by decide) (by decide) (by decide)
        · exact hh _ (by decide) (by decide) (by decide) (by decide)
        · exact hh _ (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i
        · exact (cleared_other rightPopClearSlots cap log ambient 80 (by decide) (by decide) (by decide)).trans hstack
        · exact cleared_slot rightPopClearSlots rightPopClearSlots_injective (by decide) (by decide) cap log ambient 0
        · exact cleared_slot rightPopClearSlots rightPopClearSlots_injective (by decide) (by decide) cap log ambient 1
        · exact cleared_slot rightPopClearSlots rightPopClearSlots_injective (by decide) (by decide) cap log ambient 2
        · exact cleared_slot rightPopClearSlots rightPopClearSlots_injective (by decide) (by decide) cap log ambient 3)
  rw [hheads] at hrh
  rw [ht] at hrt
  have hpop := packed_moving_path 13 0 (focused rightPopSlots PCPUnaryStackPop.machine) rfl
    (8*n+9) heads _ (cleared rightPopClearSlots cap log ambient) _ ⟨r,hrun,hrh,hrt⟩
    (by intro q scanned; simp [next])
  have hpath := hclear.trans hpop
  have he : (2*cap+5)+(8*n+9+1)=2*cap+8*n+15 := by omega
  rw [he] at hpath
  exact hpath

theorem WorkBound.rightPopped {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (n z : ℕ) (pre : List Bool)
    (hfit : pre.length+2*n+1+z≤cap) : WorkBound cap (rightPopped n cap z log pre ambient) := by
  apply (hb.clear rightPopClearSlots rightPopClearSlots_injective (by decide) (by decide)).install rightPopSlots
  intro i _ _
  fin_cases i
  · change (pre++List.replicate (2*n+1+z) false).length≤cap
    simp only [List.length_append,List.length_replicate]
    omega
  · change (ZeroPadding.pad cap (frame (List.replicate n true))).length≤cap
    rw [ZeroPadding.pad_length,frame_length,List.length_replicate]
    exact max_le le_rfl (by omega)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]
  · change (ZeroPadding.pad cap (List.replicate n true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le le_rfl (by omega)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

theorem WorkingHeads.rightPopped {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (pre : List Bool) : WorkingHeads (installedHeads rightPopSlots heads (PCPUnaryStackPop.heads pre)) := by
  apply hh.install rightPopSlots
  intro i _ h80 _ _
  fin_cases i
  · exact False.elim (h80 rfl)
  · rfl
  · rfl
  · rfl
  · rfl

end NearCubicWires.RepairOrdinary.PCPTraversal

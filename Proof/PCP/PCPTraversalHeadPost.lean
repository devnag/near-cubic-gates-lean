import Proof.PCP.PCPTraversalStackPost

/-! Retained source/count cursors and logical stack tops of the four checked
nonempty traversal branches. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def LowHeads (heads : Fin 128 → ℕ) : Prop :=
  ∀ i,i.val<39 → i≠0 → i≠2 → heads i=0
theorem LowHeads.install {t : ℕ} {heads : Fin 128 → ℕ} (hh : LowHeads heads)
    (slot : Fin t → Fin 128) (localHeads : Fin t → ℕ)
    (hs : ∀ j,slot j=0 ∨ 39 ≤ (slot j).val) : LowHeads (installedHeads slot heads localHeads) := by
  intro i hi h0 h2
  rw [installedHeads_other slot heads localHeads i (by
    intro j he
    rcases hs j with hz|hl
    · exact h0 (he.symm.trans hz)
    · rw [he] at hl
      omega)]
  exact hh i hi h0 h2

theorem low_advance {heads : Fin 128 → ℕ} (hh : LowHeads heads) (pre bits : List Bool) :
    LowHeads (installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0]) := by
  apply hh.install
  intro j; fin_cases j <;> decide
theorem low_descend {heads : Fin 128 → ℕ} (hh : LowHeads heads)
    (n : ℕ) (rightStack continuation : List Bool) : LowHeads (descendHeads n rightStack continuation heads) := by
  apply (hh.install rightPushSlots (rightPushHeads (n/2) rightStack) (by intro j; fin_cases j <;> decide)).install
  intro j; fin_cases j; decide
theorem low_resume {heads : Fin 128 → ℕ} (hh : LowHeads heads)
    (bits leftStack rightStack : List Bool) : LowHeads (resumeRightHeads bits leftStack rightStack heads) := by
  apply (hh.install saveLeftSlots (saveLeftHeads bits leftStack) (by intro j; fin_cases j <;> decide)).install
  intro j; fin_cases j <;> decide
theorem low_combine_return {heads : Fin 128 → ℕ} (hh : LowHeads heads)
    (pre continuation : List Bool) : LowHeads (combineReturnHeads pre continuation heads) := by
  apply (hh.install ![81] (fun _ => continuation.length) (by intro j; fin_cases j; decide)).install
  intro j; fin_cases j <;> decide

theorem advance_head_other (heads : Fin 128 → ℕ) (pre bits : List Bool) (i : Fin 128)
    (hi : i=2 ∨ i=28 ∨ i=80 ∨ i=81 ∨ i=82) :
    installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0] i=heads i := by
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals exact installedHeads_other advanceSlots heads _ _ (by decide)
theorem advance_head_source (heads : Fin 128 → ℕ) (pre bits : List Bool) :
    installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0] 0=pre.length+2*bits.length+1 :=
  installedHeads_slot advanceSlots advanceSlots_injective heads _ 0

theorem descend_head_other (heads : Fin 128 → ℕ) (n : ℕ) (rightStack continuation : List Bool)
    (i : Fin 128) (hi : i=0 ∨ i=2 ∨ i=28 ∨ i=82) :
    descendHeads n rightStack continuation heads i=heads i := by
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp (disch := decide) only [descendHeads,installedHeads_other]
theorem descend_head_right (heads : Fin 128 → ℕ) (n : ℕ) (rightStack continuation : List Bool) :
    descendHeads n rightStack continuation heads 80=rightStack.length+2*(n/2)+1 := by
  simp (disch := decide) only [descendHeads,installedHeads_other]
  exact installedHeads_slot rightPushSlots rightPushSlots_injective heads (rightPushHeads (n/2) rightStack) 1
theorem descend_head_continuation (heads : Fin 128 → ℕ) (n : ℕ) (rightStack continuation : List Bool) :
    descendHeads n rightStack continuation heads 81=continuation.length+2 :=
  installedHeads_slot ![81] (by decide)
    (installedHeads rightPushSlots heads (rightPushHeads (n/2) rightStack)) (fun _ => continuation.length+2) 0

theorem resume_head_other (heads : Fin 128 → ℕ) (bits leftStack rightStack : List Bool)
    (i : Fin 128) (hi : i=0 ∨ i=2 ∨ i=28 ∨ i=81) :
    resumeRightHeads bits leftStack rightStack heads i=heads i := by
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp (disch := decide) only [resumeRightHeads,installedHeads_other]
theorem resume_head_left (heads : Fin 128 → ℕ) (bits leftStack rightStack : List Bool) :
    resumeRightHeads bits leftStack rightStack heads 82=leftStack.length+2*bits.length+1 := by
  simp (disch := decide) only [resumeRightHeads,installedHeads_other]
  exact installedHeads_slot saveLeftSlots saveLeftSlots_injective heads (saveLeftHeads bits leftStack) 1
theorem resume_head_right (heads : Fin 128 → ℕ) (bits leftStack rightStack : List Bool) :
    resumeRightHeads bits leftStack rightStack heads 80=rightStack.length :=
  installedHeads_slot rightPopSlots rightPopSlots_injective
    (installedHeads saveLeftSlots heads (saveLeftHeads bits leftStack)) (PCPUnaryStackPop.heads rightStack) 0

theorem combine_head_other (heads : Fin 128 → ℕ) (pre continuation : List Bool)
    (i : Fin 128) (hi : i=0 ∨ i=2 ∨ i=28 ∨ i=80) :
    combineReturnHeads pre continuation heads i=heads i := by
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp (disch := decide) only [combineReturnHeads,installedHeads_other]
theorem combine_head_left (heads : Fin 128 → ℕ) (pre continuation : List Bool) :
    combineReturnHeads pre continuation heads 82=pre.length :=
  installedHeads_slot leftPopSlots leftPopSlots_injective
    (installedHeads ![81] heads (fun _ => continuation.length)) ![pre.length,0,0] 0
theorem combine_head_continuation (heads : Fin 128 → ℕ) (pre continuation : List Bool) :
    combineReturnHeads pre continuation heads 81=continuation.length := by
  simp (disch := decide) only [combineReturnHeads,installedHeads_other]
  exact installedHeads_slot ![81] (by decide) heads (fun _ => continuation.length) 0

end NearCubicWires.RepairOrdinary.PCPTraversal

import Proof.PCP.PCPTraversalSplit

/-! The pending-right count is physically pushed by controller16→18.
Retained stack capacity transports only zero padding; the log is actually
cleared by node16 before the push. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rightPushSlots : Fin 3 → Fin 128 := ![86,80,92]
def rightPushClearSlots : Fin 1 → Fin 128 := ![92]
theorem rightPushSlots_injective : Function.Injective rightPushSlots := by decide
theorem rightPushClearSlots_injective : Function.Injective rightPushClearSlots := by decide

def rightPushInput (n cap stackCap : ℕ) (stack : List Bool) : Configuration 3 6 :=
  ⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
    ![ZeroPadding.pad cap (List.replicate n true),ZeroPadding.pad stackCap stack,
      List.replicate cap false]⟩
def rightPushLocal (n cap stackCap : ℕ) (stack : List Bool) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (List.replicate n true),
    ZeroPadding.pad stackCap (stack++(frame (List.replicate n true)).reverse),List.replicate cap false]
def rightPushHeads (n : ℕ) (stack : List Bool) : Fin 3 → ℕ := ![0,stack.length+2*n+1,0]
noncomputable def rightPushed (n cap stackCap log : ℕ) (stack : List Bool)
    (ambient : Fin 128 → List Bool) :=
  install rightPushSlots (cleared rightPushClearSlots cap log ambient) (rightPushLocal n cap stackCap stack)

theorem padded_right_push_run (n cap stackCap : ℕ) (stack : List Bool) (hc : 2*n+2≤cap) :
    ∃ r,runFrom PCPUnaryStackPush.machine (4*n+6) (rightPushInput n cap stackCap stack)=some r ∧
      r.final.tapes=rightPushLocal n cap stackCap stack ∧
      r.final.heads=rightPushHeads n stack ∧ r.steps=4*n+6 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := PCPUnaryStackPush.push_run n stack
  let caps : Fin 3 → ℕ := ![cap,stackCap,cap]
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config PCPUnaryStackPush.machine caps _ _ base hr
  have he : ZeroPadding.config caps (PCPUnaryStackPush.entry n stack)=rightPushInput n cap stackCap stack := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    change (fun i => ZeroPadding.pad (caps i) (base.final.tapes i))=_
    rw [ht]
    funext i
    fin_cases i
    · rfl
    · rfl
    · change ZeroPadding.pad cap (List.replicate (2*n+2) false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · rw [hf]
    exact hh

theorem right_push_path (n cap stackCap log : ℕ) (stack : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 2*n+2≤cap) (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hcount : ambient 86=ZeroPadding.pad cap (List.replicate n true))
    (hstack : ambient 80=ZeroPadding.pad stackCap stack)
    (hstackHead : heads 80=stack.length) (hhd : heads 28=0) :
    Path 16 18 (2*cap+4*n+12) heads ambient
      (installedHeads rightPushSlots heads (rightPushHeads n stack))
      (rightPushed n cap stackCap log stack ambient) := by
  have hclear := clear_path 16 17 rightPushClearSlots rfl (by intro q scanned; simp [next])
    rightPushClearSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i; exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i; exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨base,hr,ht,hheads,_⟩ := padded_right_push_run n cap stackCap stack hc
  obtain ⟨r,hrun,_,hrh,hrt,_⟩ := focused_run_at PCPUnaryStackPush.machine rightPushSlots
    rightPushSlots_injective heads (cleared rightPushClearSlots cap log ambient)
    (rightPushInput n cap stackCap stack) base hr rfl
    (by intro i; fin_cases i
        · exact hh _ (by decide) (by decide) (by decide) (by decide)
        · exact hstackHead
        · exact hh _ (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i
        · exact (cleared_other rightPushClearSlots cap log ambient 86 (by decide) (by decide) (by decide)).trans hcount
        · exact (cleared_other rightPushClearSlots cap log ambient 80 (by decide) (by decide) (by decide)).trans hstack
        · exact cleared_slot rightPushClearSlots rightPushClearSlots_injective (by decide) (by decide) cap log ambient 0)
  rw [hheads] at hrh
  rw [ht] at hrt
  have hpush := packed_moving_path 17 18 (focused rightPushSlots PCPUnaryStackPush.machine) rfl
    (4*n+6) heads _ (cleared rightPushClearSlots cap log ambient) _ ⟨r,hrun,hrh,hrt⟩
    (by intro q scanned; simp [next])
  have hpath := hclear.trans hpush
  have he : (2*cap+5)+(4*n+6+1)=2*cap+4*n+12 := by omega
  rw [he] at hpath
  exact hpath

theorem right_push_stack (n cap stackCap log : ℕ) (stack : List Bool)
    (ambient : Fin 128 → List Bool) :
    rightPushed n cap stackCap log stack ambient 80=
      ZeroPadding.pad stackCap (stack++(frame (List.replicate n true)).reverse) :=
  install_slot rightPushSlots rightPushSlots_injective _ (rightPushLocal n cap stackCap stack) 1

theorem WorkingHeads.install {t : ℕ} {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (slot : Fin t → Fin 128) (localHeads : Fin t → ℕ)
    (hl : ∀ j,39 ≤ (slot j).val → slot j≠80 → slot j≠81 → slot j≠82 → localHeads j=0) :
    WorkingHeads (installedHeads slot heads localHeads) := by
  intro i hi h80 h81 h82
  cases hp : RecoveryFocus.pick slot i with
  | none => simpa only [installedHeads,hp] using hh i hi h80 h81 h82
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simpa only [installedHeads,hp] using hl j (he ▸ hi) (he ▸ h80) (he ▸ h81) (he ▸ h82)

theorem WorkingHeads.rightPush {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (n : ℕ) (stack : List Bool) : WorkingHeads (installedHeads rightPushSlots heads (rightPushHeads n stack)) := by
  apply hh.install rightPushSlots
  intro j _ h80 _ _
  fin_cases j
  · rfl
  · exact False.elim (h80 rfl)
  · rfl

theorem WorkBound.rightPushed {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (n stackCap : ℕ) (stack : List Bool)
    (hstackCap : stackCap≤cap) (hfit : stack.length+2*n+1≤cap) :
    WorkBound cap (rightPushed n cap stackCap log stack ambient) := by
  apply (hb.clear rightPushClearSlots rightPushClearSlots_injective (by decide) (by decide)).install rightPushSlots
  intro i _ _
  fin_cases i
  · change (ZeroPadding.pad cap (List.replicate n true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le le_rfl (by omega)
  · change (ZeroPadding.pad stackCap (stack++(frame (List.replicate n true)).reverse)).length≤cap
    rw [ZeroPadding.pad_length,List.length_append,List.length_reverse,frame_length,List.length_replicate]
    exact max_le hstackCap (by omega)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

end NearCubicWires.RepairOrdinary.PCPTraversal

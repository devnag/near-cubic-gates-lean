import Proof.PCP.PCPTraversalRightPush

/-! The fixed internal branch physically pushes its false continuation and
copies the computed left count before returning to the subtree test. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def continuationPushed (stackCap : ℕ) (stack : List Bool)
    (ambient : Fin 128 → List Bool) :=
  install ![81] ambient (fun _ => ZeroPadding.pad stackCap (stack++[false,true]))

theorem continuation_push_path (stackCap : ℕ) (stack : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (ht : ambient 81=ZeroPadding.pad stackCap stack) (hh : heads 81=stack.length) :
    Path 18 19 3 heads ambient
      (installedHeads ![81] heads (fun _ => stack.length+2))
      (continuationPushed stackCap stack ambient) := by
  obtain ⟨base,hr,hf,_⟩ := PCPControlOps.push_run stack stackCap
  obtain ⟨r,hrun,_,hrh,hrt,_⟩ := focused_run_at PCPControlOps.pushMachine ![81] (by decide)
    heads ambient _ base hr rfl (by intro i; fin_cases i; exact hh)
    (by intro i; fin_cases i; exact ht)
  rw [hf] at hrh hrt
  have he : (stack++[false,true]).length=stack.length+2 := by simp
  change r.final.heads=installedHeads ![81] heads (fun _ => (stack++[false,true]).length) at hrh
  rw [he] at hrh
  exact packed_moving_path 18 19 (focused ![81] PCPControlOps.pushMachine) rfl 2 heads _
    ambient _ ⟨r,hrun,hrh,hrt⟩ (by intro q scanned; simp [next])

theorem WorkBound.continuationPushed {cap : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (stackCap : ℕ) (stack : List Bool)
    (hstackCap : stackCap≤cap) (hfit : stack.length+2≤cap) :
    WorkBound cap (continuationPushed stackCap stack ambient) := by
  apply hb.install ![81]
  intro i _ _
  rw [ZeroPadding.pad_length,List.length_append]
  exact max_le hstackCap hfit
theorem WorkingHeads.continuationPushed {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (stack : List Bool) : WorkingHeads (installedHeads ![81] heads (fun _ => stack.length+2)) := by
  apply hh.install ![81]
  intro i _ _ h81 _
  fin_cases i
  exact False.elim (h81 rfl)

def leftCopyClearSlots : Fin 2 → Fin 128 := ![79,96]
def leftCopySlots : Fin 3 → Fin 128 := ![85,79,96]
theorem leftCopyClearSlots_injective : Function.Injective leftCopyClearSlots := by decide
theorem leftCopySlots_injective : Function.Injective leftCopySlots := by decide
def leftCopyLocal (n cap : ℕ) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (List.replicate n true),ZeroPadding.pad cap (List.replicate n true),
    List.replicate cap false]
noncomputable def leftCopied (n cap log : ℕ) (ambient : Fin 128 → List Bool) :=
  install leftCopySlots (cleared leftCopyClearSlots cap log ambient) (leftCopyLocal n cap)

theorem left_copy_path (n cap log : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : n+1≤cap) (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hleft : ambient 85=ZeroPadding.pad cap (List.replicate n true))
    (hhd : heads 28=0) :
    Path 19 0 (2*cap+2*n+10) heads ambient heads (leftCopied n cap log ambient) := by
  have hclear := clear_path 19 20 leftCopyClearSlots rfl (by intro q scanned; simp [next])
    leftCopyClearSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i <;> exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  have hready := PCPUnaryCopy.copy_ready n cap cap cap
  have hout : (![ZeroPadding.pad cap (List.replicate n true),
      ZeroPadding.pad cap (List.replicate n true),List.replicate (max cap (n+1)) false] : Fin 3 → List Bool)=
      leftCopyLocal n cap := by
    rw [max_eq_left hc]
    rfl
  rw [hout] at hready
  obtain ⟨r,hr,hrh,hrt,_⟩ := hready.focus_at leftCopySlots leftCopySlots_injective heads
    (cleared leftCopyClearSlots cap log ambient)
    (by intro i; fin_cases i
        · exact (cleared_other leftCopyClearSlots cap log ambient 85 (by decide) (by decide) (by decide)).trans hleft
        · exact cleared_slot leftCopyClearSlots leftCopyClearSlots_injective (by decide) (by decide) cap log ambient 0
        · exact cleared_slot leftCopyClearSlots leftCopyClearSlots_injective (by decide) (by decide) cap log ambient 1)
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
  have hcopy := packed_path 20 0 (focused leftCopySlots PCPUnaryCopy.machine) rfl (2*n+4) heads
    (cleared leftCopyClearSlots cap log ambient) _ ⟨r,hr,hrh,hrt⟩ (by intro q scanned; simp [next])
  have hpath := hclear.trans hcopy
  have he : (2*cap+5)+(2*n+4+1)=2*cap+2*n+10 := by omega
  rw [he] at hpath
  exact hpath

theorem leftCopied_count (n cap log : ℕ) (ambient : Fin 128 → List Bool) :
    leftCopied n cap log ambient 79=ZeroPadding.pad cap (List.replicate n true) :=
  install_slot leftCopySlots leftCopySlots_injective _ (leftCopyLocal n cap) 1

theorem WorkBound.leftCopied {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (n : ℕ) (hn : n≤cap) : WorkBound cap (leftCopied n cap log ambient) := by
  apply (hb.clear leftCopyClearSlots leftCopyClearSlots_injective (by decide) (by decide)).install leftCopySlots
  intro i _ _
  fin_cases i
  · change (ZeroPadding.pad cap (List.replicate n true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le le_rfl hn
  · change (ZeroPadding.pad cap (List.replicate n true)).length≤cap
    rw [ZeroPadding.pad_length,List.length_replicate]
    exact max_le le_rfl hn
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

end NearCubicWires.RepairOrdinary.PCPTraversal

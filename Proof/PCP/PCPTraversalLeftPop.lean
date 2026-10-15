import Proof.PCP.PCPTraversalOperandReady

/-! Controller21→23 clears operand scratch and physically pops the saved
left-child code. The right-child result on77 remains at its ready cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftPopClearSlots : Fin 4 → Fin 128 := ![83,84,90,92]
def leftPopSlots : Fin 3 → Fin 128 := ![82,83,92]
theorem leftPopClearSlots_injective : Function.Injective leftPopClearSlots := by decide
theorem leftPopSlots_injective : Function.Injective leftPopSlots := by decide
def leftPopInput (bits pre : List Bool) (cap z : ℕ) : Configuration 3 6 :=
  ⟨PCPStackReady.machine.start,![pre.length+2*bits.length+1,0,0],
    ![pre++(frame bits).reverse++List.replicate z false,List.replicate cap false,List.replicate cap false]⟩
def leftPopLocal (bits pre : List Bool) (cap z : ℕ) : Fin 3 → List Bool :=
  ![pre++List.replicate (2*bits.length+1+z) false,ZeroPadding.pad cap (frame bits),List.replicate cap false]
noncomputable def leftPopped (bits pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) :=
  install leftPopSlots (cleared leftPopClearSlots cap log ambient) (leftPopLocal bits pre cap z)

theorem padded_left_pop_run (bits pre : List Bool) (cap z : ℕ) (hc : 2*bits.length+2≤cap) :
    ∃ r,runFrom PCPStackReady.machine (4*bits.length+6) (leftPopInput bits pre cap z)=some r ∧
      r.final.tapes=leftPopLocal bits pre cap z ∧ r.final.heads=![pre.length,0,0] ∧
      r.steps=4*bits.length+6 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := PCPStackReady.pop_run bits pre z
  let caps : Fin 3 → ℕ := ![0,cap,cap]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config PCPStackReady.machine caps _ _ base hr
  have he : ZeroPadding.config caps (PCPStackReady.popInput bits pre z)=leftPopInput bits pre cap z := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i
      · change pre.length+(frame bits).length=pre.length+2*bits.length+1
        rw [frame_length]
        omega
      · rfl
      · rfl
    · funext i; fin_cases i
      · exact ZeroPadding.pad_zero _
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
    · change ZeroPadding.pad cap (List.replicate (2*bits.length+2) false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · rw [hfinal]
    exact hh

theorem left_pop_path (bits pre : List Bool) (cap z log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 2*bits.length+2≤cap) (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hstack : ambient 82=pre++(frame bits).reverse++List.replicate z false)
    (hstackHead : heads 82=pre.length+2*bits.length+1) (hhd : heads 28=0) :
    Path 21 23 (2*cap+4*bits.length+12) heads ambient
      (installedHeads leftPopSlots heads ![pre.length,0,0]) (leftPopped bits pre cap z log ambient) := by
  have hclear := clear_path 21 22 leftPopClearSlots rfl (by intro q scanned; simp [next])
    leftPopClearSlots_injective (by decide) (by decide) cap log heads ambient
    (by intro i; fin_cases i <;> exact hb _ (by decide) (by decide)) hdriver hlog
    (by intro i; fin_cases i <;> exact hh _ (by decide) (by decide) (by decide) (by decide))
    hhd (hh 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨base,hr,ht,hheads,_⟩ := padded_left_pop_run bits pre cap z hc
  obtain ⟨r,hrun,_,hrh,hrt,_⟩ := focused_run_at PCPStackReady.machine leftPopSlots leftPopSlots_injective
    heads (cleared leftPopClearSlots cap log ambient) _ base hr rfl
    (by intro i; fin_cases i
        · exact hstackHead
        · exact hh _ (by decide) (by decide) (by decide) (by decide)
        · exact hh _ (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i
        · exact (cleared_other leftPopClearSlots cap log ambient 82 (by decide) (by decide) (by decide)).trans hstack
        · exact cleared_slot leftPopClearSlots leftPopClearSlots_injective (by decide) (by decide) cap log ambient 0
        · exact cleared_slot leftPopClearSlots leftPopClearSlots_injective (by decide) (by decide) cap log ambient 3)
  rw [hheads] at hrh
  rw [ht] at hrt
  have hpop := packed_moving_path 22 23 (focused leftPopSlots PCPStackReady.machine) rfl
    (4*bits.length+6) heads _ (cleared leftPopClearSlots cap log ambient) _ ⟨r,hrun,hrh,hrt⟩
    (by intro q scanned; simp [next])
  have hpath := hclear.trans hpop
  have he : (2*cap+5)+(4*bits.length+6+1)=2*cap+4*bits.length+12 := by omega
  rw [he] at hpath
  exact hpath

theorem WorkBound.leftPopped {cap log : ℕ} {ambient : Fin 128 → List Bool}
    (hb : WorkBound cap ambient) (bits pre : List Bool) (z : ℕ)
    (hfit : pre.length+2*bits.length+1+z≤cap) : WorkBound cap (leftPopped bits pre cap z log ambient) := by
  apply (hb.clear leftPopClearSlots leftPopClearSlots_injective (by decide) (by decide)).install leftPopSlots
  intro i _ _
  fin_cases i
  · change (pre++List.replicate (2*bits.length+1+z) false).length≤cap
    simp only [List.length_append,List.length_replicate]
    omega
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl (by omega)
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

theorem WorkingHeads.leftPopped {heads : Fin 128 → ℕ} (hh : WorkingHeads heads)
    (pre : List Bool) : WorkingHeads (installedHeads leftPopSlots heads ![pre.length,0,0]) := by
  apply hh.install leftPopSlots
  intro i _ _ _ h82
  fin_cases i
  · exact False.elim (h82 rfl)
  · rfl
  · rfl

end NearCubicWires.RepairOrdinary.PCPTraversal

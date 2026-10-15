import Proof.PCP.PCPTraversalLeftPop

/-! Both canonical child operands are physically loaded inside21→24. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rightCopySlots : Fin 3 → Fin 128 := ![77,84,90]
theorem rightCopySlots_injective : Function.Injective rightCopySlots := by decide
noncomputable def combineLoaded (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) :=
  install rightCopySlots (leftPopped left pre cap z log ambient) (resultLocal cap right)

theorem combine_load_path (left right pre : List Bool) (cap z log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hl : 2*left.length+2≤cap) (hr : 2*right.length+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hstack : ambient 82=pre++(frame left).reverse++List.replicate z false)
    (hstackHead : heads 82=pre.length+2*left.length+1)
    (hright : ambient 77=ZeroPadding.pad cap (frame right)) (hhd : heads 28=0) :
    Path 21 24 (6*cap+17) heads ambient (installedHeads leftPopSlots heads ![pre.length,0,0])
      (combineLoaded left right pre cap z log ambient) ∧
    WorkBound cap (combineLoaded left right pre cap z log ambient) ∧
    WorkingHeads (installedHeads leftPopSlots heads ![pre.length,0,0]) := by
  let popped := leftPopped left pre cap z log ambient
  let moved := installedHeads leftPopSlots heads ![pre.length,0,0]
  have hfit : pre.length+2*left.length+1+z≤cap := by
    have h := hb 82 (by decide) (by decide)
    rw [hstack,List.length_append,List.length_append,List.length_reverse,frame_length,List.length_replicate] at h
    omega
  have hpbound : WorkBound cap popped := hb.leftPopped left pre z hfit
  have hph : WorkingHeads moved := hh.leftPopped pre
  have hpop := left_pop_path left pre cap z log heads ambient hl hb hh hdriver hlog hstack hstackHead hhd
  have hcopy := field_copy_path 23 24 rightCopySlots rightCopySlots_injective rfl
    (by intro q scanned; simp [next]) right cap moved popped hr
    (by intro i; fin_cases i
        · exact (install_cleared_other leftPopSlots leftPopClearSlots cap log ambient
            (leftPopLocal left pre cap z) 77 (by decide) (by decide) (by decide) (by decide)).trans hright
        · exact (install_other leftPopSlots (cleared leftPopClearSlots cap log ambient)
            (leftPopLocal left pre cap z) 84 (by decide)).trans
            (cleared_slot leftPopClearSlots leftPopClearSlots_injective (by decide) (by decide) cap log ambient 1)
        · exact (install_other leftPopSlots (cleared leftPopClearSlots cap log ambient)
            (leftPopLocal left pre cap z) 90 (by decide)).trans
            (cleared_slot leftPopClearSlots leftPopClearSlots_injective (by decide) (by decide) cap log ambient 2))
    (by intro i; fin_cases i <;> exact hph _ (by decide) (by decide) (by decide) (by decide))
  exact ⟨(hpop.trans hcopy).mono (by omega),hpbound.fieldCopied rightCopySlots right hr,hph⟩

theorem combine_loaded_operands (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) :
    combineLoaded left right pre cap z log ambient 83=ZeroPadding.pad cap (frame left) ∧
    combineLoaded left right pre cap z log ambient 84=ZeroPadding.pad cap (frame right) := by
  constructor
  · exact (install_other rightCopySlots (leftPopped left pre cap z log ambient)
      (resultLocal cap right) 83 (by decide)).trans
      (install_slot leftPopSlots leftPopSlots_injective (cleared leftPopClearSlots cap log ambient)
        (leftPopLocal left pre cap z) 1)
  · exact install_slot rightCopySlots rightCopySlots_injective _ (resultLocal cap right) 1

theorem combine_loaded_driver (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) :
    combineLoaded left right pre cap z log ambient 28=List.replicate cap true :=
  (install_other rightCopySlots (leftPopped left pre cap z log ambient) (resultLocal cap right) 28 (by decide)).trans
    (install_cleared_driver leftPopSlots leftPopClearSlots leftPopClearSlots_injective
      (by decide) (by decide) cap log ambient (leftPopLocal left pre cap z) (by decide))
theorem combine_loaded_log (left right pre : List Bool) (cap z log : ℕ)
    (ambient : Fin 128 → List Bool) :
    combineLoaded left right pre cap z log ambient 127=List.replicate (max log (cap+1)) false :=
  (install_other rightCopySlots (leftPopped left pre cap z log ambient) (resultLocal cap right) 127 (by decide)).trans
    (install_cleared_log leftPopSlots leftPopClearSlots leftPopClearSlots_injective
      (by decide) (by decide) cap log ambient (leftPopLocal left pre cap z) (by decide))

end NearCubicWires.RepairOrdinary.PCPTraversal

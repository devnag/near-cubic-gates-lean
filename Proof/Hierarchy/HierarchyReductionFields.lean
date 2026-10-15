import Proof.Hierarchy.HierarchyReductionLayout

/-! The first two paid phases produce the original binary hierarchy clock
and the independent linear allocation from the same retained framed x. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem allocation_val (k : ℕ) (i : Fin 10) :
    (allocationSlots k i).val=if i.val=0 then 2 else base k+(i.val-1) := by
  unfold allocationSlots
  split_ifs <;> rfl

theorem bound_ready (k C : ℕ) (x : List Bool) :
    ∃ middle,ClockJoin.ReadyRun (boundProgram k C) (HierarchyFromInput.budget (k+2) C x)
      (input k x) middle ∧ Fields k C x middle ∧ HierarchyBound.Fresh middle (base k) := by
  obtain ⟨r,hr,hout,_,hx,hh,hs⟩ := HierarchyFromInput.from_input_run (k+2) C (by omega) x
  have h := (show ClockJoin.ReadyRun _ _ _ r.final.tapes from ⟨r,hr,rfl,hh,hs⟩).focus
    (low k) (low_injective k) (input k x) (by intro j; rfl)
  refine ⟨_,h,⟨(install_slot _ (low_injective k) _ _ _).trans hx,
    (install_slot _ (low_injective k) _ _ _).trans hout⟩,?_⟩
  apply HierarchyBound.fresh_install _ _ _ (base k) (base k) (by omega)
  · intro i hi
    have hl := base_lower k
    simp [input,show i.val≠2 by omega]
  · intro j
    exact j.isLt

theorem allocation_ready (k C Cpad : ℕ) (code x : List Bool) (ambient : Fin (tapes k) → List Bool)
    (hf : Fields k C x ambient) (hblank : HierarchyBound.Fresh ambient (base k)) :
    ∃ middle,ClockJoin.ReadyRun (allocationProgram k C Cpad code)
      (HierarchyAllocation.budget (coefficient Cpad) (constant C Cpad code) x) ambient middle ∧
      Fields k C x middle ∧ middle (extra k 7)=
        List.replicate (HierarchyBinary.allocation Cpad code.length C x.length) true ∧
      HierarchyBound.Fresh middle (base k+9) := by
  have hi : ∀ j,ambient (allocationSlots k j)=HierarchyAllocation.input x j := by
    intro j
    by_cases hj : j.val=0
    · simpa [allocationSlots,HierarchyAllocation.input,hj] using hf.1
    · simp only [HierarchyAllocation.input,if_neg hj]
      apply hblank
      rw [allocation_val,if_neg hj]
      omega
  have h := (HierarchyAllocation.allocation_ready (coefficient Cpad) (constant C Cpad code) x).focus
    (allocationSlots k) (allocation_injective k) ambient hi
  have hb := bound_bounds k
  have hl := base_lower k
  refine ⟨_,h,⟨install_slot _ (allocation_injective k) _ _ 0,?_⟩,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro j he
      have hv := congrArg Fin.val he
      rw [allocation_val] at hv
      split_ifs at hv <;> omega)]
    exact hf.2
  · have ho := install_slot (allocationSlots k) (allocation_injective k) ambient
      (HierarchyAllocation.output (coefficient Cpad) (constant C Cpad code) x) 8
    change install (allocationSlots k) ambient _ (extra k 7)=
      List.replicate (coefficient Cpad*x.length+constant C Cpad code) true at ho
    rw [allocation_value] at ho
    exact ho
  · apply HierarchyBound.fresh_install _ _ _ (base k) (base k+9) (by omega) hblank
    intro j
    rw [allocation_val]
    split_ifs <;> omega

end NearCubicWires.RepairOrdinary.HierarchyReduction

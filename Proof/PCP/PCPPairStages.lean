import Proof.PCP.PCPPairLayout
import Proof.Hierarchy.CompetitorRationalProducts

/-! Actual comparison and square phases of the fixed pair-node controller.
The multiplier consumes the original factor field, not a padded factor. -/
namespace NearCubicWires.RepairOrdinary.PCPPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initialized (left right : List Bool) : Fin 30 → List Bool :=
  fun i => if i.val=6 then [false] else input left right i
def compared (left right : List Bool) : Fin 30 → List Bool := fun i =>
  if i.val=6 then [decide (value right ≤ value left)]
  else if i.val=5 then List.replicate (2*width left right+1) false
  else input left right i

theorem operand_bounds (left right : List Bool) :
    value left<2^width left right ∧ value right<2^width left right := by
  constructor
  · exact (value_lt left).trans_le (Nat.pow_le_pow_right (by decide) (by unfold width; omega))
  · exact (value_lt right).trans_le (Nat.pow_le_pow_right (by decide) (by unfold width; omega))

theorem compare_run (left right : List Bool) :
    ReadyRun compareProgram (4*width left right+4) (initialized left right) (compared left right) := by
  obtain ⟨hl,hr⟩ := operand_bounds left right
  have h := RecoveryRootRound.compare_ready (binary (width left right) (value right))
    (binary (width left right) (value left)) 0 (by simp)
  simp only [binary_length, binary_value _ _ hl, binary_value _ _ hr,
    max_eq_right (Nat.zero_le _)] at h
  have hrun := h.focus compareSlots compare_injective (initialized left right)
    (by intro j; fin_cases j <;> rfl)
  have he : install compareSlots (initialized left right)
      ![frame (binary (width left right) (value right)),
        frame (binary (width left right) (value left)),
        [decide (value right ≤ value left)], List.replicate (2*width left right+1) false]=
      compared left right := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot compareSlots compare_injective _ _ 0
      | exact install_slot compareSlots compare_injective _ _ 1
      | exact install_slot compareSlots compare_injective _ _ 2
      | exact install_slot compareSlots compare_injective _ _ 3
      | exact install_other compareSlots _ _ _ (by decide)
  exact he ▸ hrun

def chosen (branch : Bool) (left right : List Bool) : List Bool := if branch then left else right

theorem square_run (branch : Bool) (left right : List Bool) :
    ∃ out : Fin 30 → List Bool,
      ClockJoin.ReadyRun (multiplyProgram branch)
        (HierarchyMultiplyEntry.budget (width left right) (chosen branch left right))
        (compared left right) out ∧
      out 0=input left right 0 ∧ out 1=input left right 1 ∧
      out 4=input left right 4 ∧ out 6=[decide (value right ≤ value left)] ∧
      out 10=frame (binary (width left right) (value (chosen branch left right)*value (chosen branch left right))) ∧
      (∀ i : Fin 30,21 ≤ i.val → out i=[]) := by
  have hfit : value (chosen branch left right)*2^(chosen branch left right).length<2^width left right := by
    cases branch
    · exact (square_bounds left right).2.1
    · exact (square_bounds left right).1
  obtain ⟨base,hr,hproduct,_,hnum,hwidth,_,hh,hs⟩ :=
    HierarchyMultiplyEntry.multiply_run (width left right) (value (chosen branch left right))
      (chosen branch left right) hfit
  have hslot : ∀ j,compared left right (multiplySlots branch j)=
      HierarchyMultiplyEntry.input14 (width left right) (value (chosen branch left right))
        (chosen branch left right) j := by
    intro j
    cases branch <;> fin_cases j <;> rfl
  have hready : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine
      (HierarchyMultiplyEntry.budget (width left right) (chosen branch left right))
      (HierarchyMultiplyEntry.input14 (width left right) (value (chosen branch left right))
        (chosen branch left right)) base.final.tapes := ⟨base,hr,rfl,hh,hs⟩
  let out := install (multiplySlots branch) (compared left right) base.final.tapes
  refine ⟨out,CompetitorRationalProducts.bounded_focus (multiplySlots branch)
    (multiply_injective branch) _ _ _ hready _ hslot,?_,?_,?_,?_,?_,?_⟩
  · cases branch
    · exact install_other (multiplySlots false) _ _ 0 (by decide)
    · exact (install_slot (multiplySlots true) (multiply_injective true) _ _ 8).trans hnum
  · cases branch
    · exact (install_slot (multiplySlots false) (multiply_injective false) _ _ 8).trans hnum
    · exact install_other (multiplySlots true) _ _ 1 (by decide)
  · exact (install_slot (multiplySlots branch) (multiply_injective branch) _ _ 9).trans hwidth
  · cases branch <;> exact install_other (multiplySlots _) _ _ 6 (by decide)
  · exact (install_slot (multiplySlots branch) (multiply_injective branch) _ _ 3).trans hproduct
  · intro i hi
    have hnot : ∀ j,multiplySlots branch j≠i := by
      intro j he
      have hv := congrArg Fin.val he
      simp only [multiplySlots] at hv
      split at hv
      · split at hv <;> simp at hv <;> omega
      · split at hv
        · split at hv <;> simp at hv <;> omega
        · split at hv <;> simp at hv <;> omega
    rw [show out i=compared left right i from install_other (multiplySlots branch) _ _ i hnot]
    simp only [compared,input]
    split <;> (first | omega | skip)
    split <;> (first | omega | skip)
    split <;> (first | omega | skip)
    split <;> (first | omega | skip)
    split <;> (first | omega | skip)
    split <;> (first | omega | skip)
    split <;> (first | omega | rfl)

end NearCubicWires.RepairOrdinary.PCPPair

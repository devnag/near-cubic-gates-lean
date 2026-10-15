import Proof.Hierarchy.HierarchyBound
import Proof.Hierarchy.HierarchyInputLength
import Proof.Hierarchy.HierarchyWidth

/-! A single fixed finite layout connects retained input counting, short
width generation, and the actual hierarchy-bound producer. -/
namespace NearCubicWires.RepairOrdinary.HierarchyFromInput
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := HierarchyBound.tapes D+11
theorem tapes_lower (D : ℕ) : 35≤tapes D := by
  dsimp [tapes,HierarchyBound.tapes,HierarchyPower.tapes]
  omega
def field (D : ℕ) (i : Fin 13) : Fin (tapes D) := ⟨i.val,by have := tapes_lower D; omega⟩
def countSlots (D : ℕ) (i : Fin 4) : Fin (tapes D) := ⟨i.val,by have := tapes_lower D; omega⟩
def widthSlots (D : ℕ) : Fin 10 → Fin (tapes D) := fun i =>
  if h : i.val=0 then field D 0 else ⟨i.val+3,by have := tapes_lower D; omega⟩
def boundSlots (D : ℕ) : Fin (HierarchyBound.tapes D) → Fin (tapes D) := fun i =>
  if h0 : i.val=0 then field D 0 else if h1 : i.val=1 then field D 11
  else ⟨i.val+11,by dsimp [tapes]; omega⟩
theorem width_val (D : ℕ) (i : Fin 10) :
    (widthSlots D i).val=if i.val=0 then 0 else i.val+3 := by
  unfold widthSlots
  split_ifs <;> rfl
theorem bound_val (D : ℕ) (i : Fin (HierarchyBound.tapes D)) :
    (boundSlots D i).val=if i.val=0 then 0 else if i.val=1 then 11 else i.val+11 := by
  unfold boundSlots
  split_ifs <;> rfl
theorem count_injective (D : ℕ) : Function.Injective (countSlots D) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin (tapes D) => i.val) h
theorem width_injective (D : ℕ) : Function.Injective (widthSlots D) := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [width_val] at he
  split_ifs at he <;> omega
theorem bound_injective (D : ℕ) : Function.Injective (boundSlots D) := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [bound_val] at he
  split_ifs at he <;> omega

def input (D : ℕ) (bits : List Bool) : Fin (tapes D) → List Bool := fun i =>
  if i.val=2 then frame bits else []
noncomputable def countProgram (D : ℕ) := RecoveryFocus.machine (countSlots D) HierarchyInputLength.machine
noncomputable def widthProgram (D C : ℕ) := RecoveryFocus.machine (widthSlots D) (HierarchyWidth.machine D C)
noncomputable def boundProgram (D C : ℕ) (hD : 0<D) := RecoveryFocus.machine (boundSlots D)
  (HierarchyBound.machine D C hD)

theorem count_ready (D : ℕ) (bits : List Bool) :
    ∃ middle,ClockJoin.ReadyRun (countProgram D) (HierarchyInputLength.budget bits) (input D bits) middle ∧
      middle (field D 0)=frame (ClockBinary.word bits.length) ∧
      middle (field D 2)=frame bits ∧ HierarchyBound.Fresh middle 4 := by
  obtain ⟨cap,scratch,hcap,hsc,r,hr,h0,h1,h2,h3,hh,hs⟩ := HierarchyInputLength.count_run bits
  have h := (show ClockJoin.ReadyRun _ _ _ r.final.tapes from ⟨r,hr,rfl,hh,hs⟩).focus
    (countSlots D) (count_injective D) (input D bits) (by intro j; fin_cases j <;> rfl)
  refine ⟨_,h,(install_slot _ (count_injective D) _ _ 0).trans h0,
    (install_slot _ (count_injective D) _ _ 2).trans h2,?_⟩
  apply HierarchyBound.fresh_install _ _ _ 4 4 (by omega)
  · intro i hi
    simp [input,show i.val≠2 by omega]
  · intro j
    exact j.isLt

theorem width_ready (D C : ℕ) (bits : List Bool) (ambient : Fin (tapes D) → List Bool)
    (h0 : ambient (field D 0)=frame (ClockBinary.word bits.length))
    (h2 : ambient (field D 2)=frame bits) (hblank : HierarchyBound.Fresh ambient 4) :
    ∃ middle,ClockJoin.ReadyRun (widthProgram D C) (HierarchyWidth.budget D C bits.length) ambient middle ∧
      middle (field D 0)=frame (ClockBinary.word bits.length) ∧
      middle (field D 11)=List.replicate (HierarchyBinary.width C D bits.length) true ∧
      middle (field D 2)=frame bits ∧ HierarchyBound.Fresh middle 13 := by
  have hi : ∀ j,ambient (widthSlots D j)=HierarchyWidth.input bits.length j := by
    intro j
    by_cases hj : j.val=0
    · have he : j=0 := Fin.ext hj
      subst j
      exact h0
    · simp only [HierarchyWidth.input,if_neg hj]
      apply hblank
      simp [widthSlots,hj]
      omega
  have h := (HierarchyWidth.width_ready D C bits.length).focus (widthSlots D) (width_injective D) ambient hi
  refine ⟨_,h,install_slot _ (width_injective D) _ _ 0,
    install_slot _ (width_injective D) _ _ 8,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro j he
      have hv := congrArg Fin.val he
      change (widthSlots D j).val=2 at hv
      rw [width_val] at hv
      split_ifs at hv; omega)]
    exact h2
  · apply HierarchyBound.fresh_install _ _ _ 4 13 (by omega) hblank
    intro j
    rw [width_val]
    split_ifs <;> omega

end NearCubicWires.RepairOrdinary.HierarchyFromInput

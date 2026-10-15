import Proof.Hierarchy.HierarchyFromInputLayout

/-! The hierarchy clock field is produced directly from the literal framed
input x. Counting, width generation, all arithmetic and call returns are
included in the ordinary execution receipt. -/
namespace NearCubicWires.RepairOrdinary.HierarchyFromInput
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputTape (D : ℕ) (hD : 0<D) := boundSlots D (HierarchyBound.outputTape D hD)
theorem bound_ready (D C : ℕ) (hD : 0<D) (bits : List Bool) (ambient : Fin (tapes D) → List Bool)
    (h0 : ambient (field D 0)=frame (ClockBinary.word bits.length))
    (hw : ambient (field D 11)=List.replicate (HierarchyBinary.width C D bits.length) true)
    (h2 : ambient (field D 2)=frame bits) (hblank : HierarchyBound.Fresh ambient 13) :
    ∃ middle,ClockJoin.ReadyRun (boundProgram D C hD) (HierarchyBound.budget D C bits.length) ambient middle ∧
      middle (outputTape D hD)=frame (binary (HierarchyBinary.width C D bits.length) (C*(bits.length^D+1))) ∧
      middle (field D 11)=List.replicate (HierarchyBinary.width C D bits.length) true ∧
      middle (field D 2)=frame bits := by
  obtain ⟨r,hr,hout,hwidth,hh,hs⟩ := HierarchyBound.bound_run D C bits.length hD
  have hi : ∀ j,ambient (boundSlots D j)=HierarchyBound.input D C bits.length j := by
    intro j
    by_cases hj0 : j.val=0
    · simpa [boundSlots,HierarchyBound.input,hj0] using h0
    by_cases hj1 : j.val=1
    · simpa [boundSlots,HierarchyBound.input,hj0,hj1] using hw
    simp only [HierarchyBound.input,if_neg hj0,if_neg hj1]
    apply hblank
    simp [boundSlots,hj0,hj1]
    omega
  have h := (show ClockJoin.ReadyRun _ _ _ r.final.tapes from ⟨r,hr,rfl,hh,hs⟩).focus
    (boundSlots D) (bound_injective D) ambient hi
  refine ⟨_,h,(install_slot _ (bound_injective D) _ _ _).trans hout,
    (install_slot _ (bound_injective D) _ _ (HierarchyBound.widthTape D)).trans hwidth,?_⟩
  rw [install_other _ _ _ _ (by
    intro j he
    have hv := congrArg Fin.val he
    change (boundSlots D j).val=2 at hv
    rw [bound_val] at hv
    split_ifs at hv <;> omega)]
  exact h2

noncomputable def machine (D C : ℕ) (hD : 0<D) := Composition.machine
  (Composition.machine (countProgram D) (widthProgram D C)) (boundProgram D C hD)
def budget (D C : ℕ) (bits : List Bool) := HierarchyInputLength.budget bits+1+
  HierarchyWidth.budget D C bits.length+1+HierarchyBound.budget D C bits.length

theorem from_input_run (D C : ℕ) (hD : 0<D) (bits : List Bool) :
    ∃ r,run (machine D C hD) (budget D C bits) (input D bits)=some r ∧
      r.final.tapes (outputTape D hD)=frame (binary (HierarchyBinary.width C D bits.length) (C*(bits.length^D+1))) ∧
      r.final.tapes (field D 11)=List.replicate (HierarchyBinary.width C D bits.length) true ∧
      r.final.tapes (field D 2)=frame bits ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget D C bits := by
  obtain ⟨a,ha,ha0,ha2,hab⟩ := count_ready D bits
  obtain ⟨b,hb,hb0,hbw,hb2,hbb⟩ := width_ready D C bits a ha0 ha2 hab
  obtain ⟨c,hc,hco,hcw,hc2⟩ := bound_ready D C hD bits b hb0 hbw hb2 hbb
  have h := ClockJoin.join _ _ _ _ _ _ _ ha hb
  obtain ⟨r,hr,ht,hh,hs⟩ := ClockJoin.join _ _ _ _ _ _ _ h hc
  exact ⟨r,hr,by rw [ht]; exact hco,by rw [ht]; exact hcw,by rw [ht]; exact hc2,hh,hs⟩

end NearCubicWires.RepairOrdinary.HierarchyFromInput

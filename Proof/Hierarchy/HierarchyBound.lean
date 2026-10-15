import Proof.Hierarchy.HierarchyBoundPhases

/-! Actual binary producer for B_H=C*(n^D+1). The field width is polynomial
in the short input length, and no unary B_H is created or scanned. -/
namespace NearCubicWires.RepairOrdinary.HierarchyBound
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (D C : ℕ) (hD : 0<D) := Composition.machine
  (Composition.machine (Composition.machine (powerProgram D hD) (successorProgram D hD))
    (coefficientProgram D C)) (multiplyProgram D hD)
def budget (D C n : ℕ) := HierarchyPower.fullBudget D C n+1+(8*HierarchyBinary.width C D n+9)+1+
  coefficientCost C+1+multiplyCost D C n
def outputTape (D : ℕ) (hD : 0<D) := multiplySlots D hD 3

theorem bound_run (D C n : ℕ) (hD : 0<D) :
    ∃ r,run (machine D C hD) (budget D C n) (input D C n)=some r ∧
      r.final.tapes (outputTape D hD)=frame (binary (HierarchyBinary.width C D n) (C*(n^D+1))) ∧
      r.final.tapes (widthTape D)=List.replicate (HierarchyBinary.width C D n) true ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget D C n := by
  obtain ⟨a,ha,haf,hab⟩ := power_ready D C n hD
  obtain ⟨b,hb,hbf,hbb⟩ := successor_ready D C n hD a haf hab
  obtain ⟨c,hc,hcf,hcc,hcb⟩ := coefficient_ready D C n hD b hbf hbb
  obtain ⟨d,hd,hdf,hdw⟩ := multiply_ready D C n hD c hcf hcc hcb
  have h1 := ClockJoin.join _ _ _ _ _ _ _ ha hb
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 hc
  obtain ⟨r,hr,ht,hh,hs⟩ := ClockJoin.join _ _ _ _ _ _ _ h2 hd
  exact ⟨r,hr,by rw [ht]; exact hdf,by rw [ht]; exact hdw,hh,hs⟩

theorem budget_formula (D C n : ℕ) : budget D C n=
    12*HierarchyBinary.width C D n+26+D*(128*(HierarchyBinary.width C D n+1)*(PCPResourceLedger.ell n+1)+1)+
      (4*C.bits.length+4)+128*(HierarchyBinary.width C D n+1)*(C.bits.length+1) := by
  simp only [budget,HierarchyPower.fullBudget,HierarchyPower.budget,HierarchyPower.stepBudget,
    coefficientCost,frame_length,multiplyCost]
  ring

end NearCubicWires.RepairOrdinary.HierarchyBound

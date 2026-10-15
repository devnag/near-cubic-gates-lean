import Proof.CaseAnalysis.WitnessInputPower

/-! The cold polynomial driver retains the original framed input for the
following canonical field traversal, without copying or re-encoding it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.InputPower
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_power_retained (D C offset : ℕ) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine D C offset) (budget D C offset bits) (input D bits) out ∧
      out (powerSlots D (DimensionPower.valueSlot D D le_rfl))=List.replicate (C*(bits.length+offset)^D) true ∧
      out (powerSlots D ⟨0,by simp [DimensionPower.tapes]⟩)=UnaryTemplate.tape (bits.length+offset) ∧
      out (allocationSlots D 8)=List.replicate (bits.length+offset) true ∧
      out (allocationSlots D 0)=frame bits:=by
  obtain ⟨p,hp,ht,hv⟩:=DimensionPower.power_run D C (bits.length+offset)
  have h0:=ClockJoin.join (allocation D offset) (template D) _ _ _ _ _
    (allocation_ready D offset bits) (template_ready D offset bits)
  have h1:=hp.focus (powerSlots D) (power_injective D) (templated D offset bits) (power_input D offset bits)
  have h:=ClockJoin.join (first D offset) (power D C) _ _ _ _ _ h0 h1
  refine ⟨_,h,?_,?_,?_,?_⟩
  · rw [install_slot _ (power_injective D)]
    exact hv
  · rw [install_slot _ (power_injective D)]
    exact ht
  · rw [install_other _ _ _ _ (power_outside D _ (by simp [allocationSlots]))]
    have he:allocationSlots D 8=templateSlots D 0:=by apply Fin.ext;rfl
    rw [he,templated,install_slot _ (template_injective D)]
    rfl
  · rw [install_other _ _ _ _ (power_outside D _ (by simp [allocationSlots])),templated,
      install_other _ _ _ _ (by intro i;fin_cases i <;> simp [templateSlots,allocationSlots,Fin.ext_iff])]
    simp [allocated,allocationSlots,HierarchyAllocation.output,HierarchyAllocation.afterConstant,
      HierarchyAllocation.afterProduct,HierarchyAllocation.afterEll,HierarchyAllocation.afterDegree,
      HierarchyAllocation.input]

end NearCubicWires.RepairOrdinary.CloseoutWitness.InputPower

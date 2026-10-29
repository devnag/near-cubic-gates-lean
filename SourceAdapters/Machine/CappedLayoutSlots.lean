import SourceAdapters.Machine.CappedLayout

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: disjoint physical slots for bounded simulation and result printing. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

theorem prepared_output_val (p : Program) :
    (preparedSlot p (preparedOutputSlot p)).val=8+p.outputTape.val := by
  have hi := p.outputTape.isLt
  have hn := p.outputFresh
  simp only [preparedSlot,preparedOutputSlot,Fin.val_castAdd,Fin.val_castSucc]
  split_ifs <;> omega

theorem prepared_marker_val (p : Program) :
    (preparedSlot p (preparedMarkerSlot p)).val=8+(p.tapeCount+1) := by
  simp [preparedSlot,preparedMarkerSlot]

theorem prepared_clock_val (p : Program) :
    (preparedSlot p (preparedClockSlot p)).val=2 := by
  have hp := p.twoTapes
  simp only [preparedSlot,preparedClockSlot,Fin.val_castAdd,Fin.val_last]
  split_ifs <;> omega

theorem prepared_status_val (p : Program) :
    (preparedSlot p (preparedStatusSlot p)).val=3 := by
  simp [preparedSlot,preparedStatusSlot]
  omega

theorem resultSlot_val (p : Program) (i : Fin 6) :
    (resultSlot p i).val = ![8+p.outputTape.val,8+(p.tapeCount+4),8+(p.tapeCount+5),
      8+(p.tapeCount+1),2,3] i := by
  fin_cases i <;> simp [resultSlot,prepared_output_val,prepared_marker_val,prepared_clock_val,
    prepared_status_val,outputSlot,originSlot]

theorem resultSlot_injective (p : Program) : Function.Injective (resultSlot p) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [resultSlot_val,resultSlot_val] at hv
  have hp := p.twoTapes
  have hi := p.outputTape.isLt
  fin_cases i <;> fin_cases j <;> simp at hv ⊢ <;> omega

noncomputable def result (p : Program) := RecoveryFocus.machine (resultSlot p) ResultWriter.machine
noncomputable def core (p : Program) := Composition.machine (prepared p) (result p)
noncomputable def machine (p : Program) := Composition.machine (loader p) (core p)

end NearCubicGates.Adapters.Machine.Capped.Layout

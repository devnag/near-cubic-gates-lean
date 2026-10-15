import Proof.CaseAnalysis.CaseTwoTraversalController
import Proof.PCP.PCPPNativeForwardScalar
import Proof.Assembly.AppendOutputLength

/-! The actual native stream only moves right. The existing measured-output
wrapper can therefore produce its physical length and rewind it once. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_native_forward : CursorRestore.NoLeft FieldNative.machine 21:=by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.unselected_forward FieldNative.sliceSlots _ 21 (by decide)
  · exact CursorRestore.focus_forward FieldNative.nativeSlots (by decide)
      PCPPNativeNaturalAppend.machine 17 PCPPNativeForward.natural

theorem field_ready_forward : CursorRestore.NoLeft FieldReady.machine 21:=
  PCPPNativeForward.masked FieldNative.machine FieldReady.selected 21 (by decide) field_native_forward

theorem field_clear_forward : CursorRestore.NoLeft FieldClear.machine 21:=by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward FieldClear.old FieldClear.old_injective FieldReady.machine 21 field_ready_forward
  · exact EquationRowCuts.unselected_forward FieldClear.eraseSlots _ 21 (by decide)

theorem field_step_forward : CursorRestore.NoLeft FieldStep.machine 21:=by
  apply CursorRestore.composition_forward
  · exact field_clear_forward
  · exact EquationRowCuts.unselected_forward FieldStep.advanceSlots _ 21 (by decide)

theorem field_forward : CursorRestore.NoLeft field 27:=
  CursorRestore.focus_forward fieldSlots field_injective FieldStep.machine 21 field_step_forward

theorem native_copy_forward : CursorRestore.NoLeft NativeCopy.machine 2:=
  PCPPNativeForward.masked (PCPPQueryField.machine true) NativeCopy.selected 2 (by decide)
    EquationRowRaw.header_field_forward

theorem tag_publish_forward : CursorRestore.NoLeft TagPublish.machine 27:=by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward TagPublish.copySlots (by decide) NativeCopy.machine 2 native_copy_forward
  · exact EquationRowCuts.unselected_forward TagPublish.clearSlots _ 27 (by decide)

theorem publish_forward : CursorRestore.NoLeft publish 27:=
  CursorRestore.focus_forward publishSlots publish_injective TagPublish.machine 27 tag_publish_forward

theorem node_forward : CursorRestore.NoLeft node 27:=by
  apply CursorRestore.composition_forward
  · exact publish_forward
  · apply CursorRestore.composition_forward
    · exact CursorRestore.composition_forward field field 27 field_forward field_forward
    · exact EquationRowCuts.unselected_forward countSlots _ 27 (by decide)

theorem tag_forward : CursorRestore.NoLeft tag 27:=
  EquationRowCuts.unselected_forward tagSlots _ 27 (by decide)

theorem forward : CursorRestore.NoLeft machine 27:=by
  apply EquationCut.calls_forward
  intro j
  fin_cases j
  · exact tag_forward
  · exact node_forward
  · exact field_forward

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal

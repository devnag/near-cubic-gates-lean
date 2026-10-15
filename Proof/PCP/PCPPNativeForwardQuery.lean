import Proof.PCP.PCPPNativeForwardNode

/-! The entire checked reusable query bank has a forward live output,
including all resets, erasures, row loads and actual R/Q driver loops. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeForward
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_reset : CursorRestore.NoLeft PCPPNativeNodeReset.machine 5 :=
  masked PCPPNativeNodeMachine.machine PCPPNativeNodeReset.selected 5 (by decide) node
theorem node_reusable : CursorRestore.NoLeft PCPPNativeNodeReusable.machine 5 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward PCPPNativeNodeReusable.resetSlots (by decide) _ 5 node_reset
  · exact EquationRowCuts.unselected_forward PCPPNativeNodeReusable.eraseSlots _ 5 (by
      intro i; apply Fin.ne_of_val_ne; change i.val+6≠5; omega)
theorem node_step : CursorRestore.NoLeft PCPPNativeNodeStep.machine 5 :=
  CursorRestore.composition_forward _ _ _ node_reusable
    (EquationRowCuts.unselected_forward PCPPNativeNodeStep.advanceSlots _ 5 (by decide))
theorem node_loop : CursorRestore.NoLeft PCPPNativeNodeLoop.machine 5 :=
  CursorRestore.repeat_forward PCPPNativeNodeStep.machine PCPPNativeNodeLoop.accepted 5 node_step

theorem query_header : CursorRestore.NoLeft PCPPNativeQuery.header 5 :=
  EquationRowCuts.unselected_forward PCPPNativeQuery.headerSlots _ 5 (by decide)
theorem query_nodes : CursorRestore.NoLeft PCPPNativeQuery.nodes 5 :=
  CursorRestore.focus_forward PCPPNativeQuery.loopSlots PCPPNativeQuery.loop_injective _ 5 node_loop
theorem query_footer : CursorRestore.NoLeft PCPPNativeQuery.footer 5 :=
  EquationRowCuts.unselected_forward PCPPNativeQuery.footerSlots _ 5 (by decide)
theorem query_value : CursorRestore.NoLeft PCPPNativeQuery.value 5 :=
  EquationRowCuts.unselected_forward PCPPNativeQuery.valueSlots _ 5 (by decide)
theorem query_last : CursorRestore.NoLeft PCPPNativeQuery.tail 5 :=
  CursorRestore.focus_forward PCPPNativeQuery.tailSlots PCPPNativeQuery.tail_injective _ 20 query_tail
theorem query_body : CursorRestore.NoLeft PCPPNativeQuery.body 5 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (CursorRestore.composition_forward _ _ _
        (CursorRestore.composition_forward _ _ _ query_header query_nodes) query_footer) query_value) query_last
theorem query_step : CursorRestore.NoLeft PCPPNativeQueryStep.machine 5 :=
  CursorRestore.composition_forward _ _ _ query_body
    (EquationRowCuts.unselected_forward PCPPNativeQueryStep.advanceSlots _ 5 (by decide))
theorem query_reset : CursorRestore.NoLeft PCPPNativeQueryReset.machine 5 :=
  masked PCPPNativeQueryStep.machine PCPPNativeQueryReset.selected 5 (by decide) query_step
theorem query_reusable : CursorRestore.NoLeft PCPPNativeQueryReusable.machine 5 := by
  apply CursorRestore.composition_forward
  · exact CursorRestore.focus_forward PCPPNativeQueryReusable.resetSlots (by
      intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 171 => k.val) h)
      _ 5 query_reset
  · exact EquationRowCuts.unselected_forward PCPPNativeQueryReusable.eraseSlots _ 5 (by decide)
theorem query_iteration : CursorRestore.NoLeft PCPPNativeQueryIteration.machine 5 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward PCPPNativeQueryIteration.loadSlots _ 5 (by decide))
    (CursorRestore.focus_forward PCPPNativeQueryIteration.querySlots PCPPNativeQueryIteration.query_injective
      _ 5 query_reusable)
theorem query_bank : CursorRestore.NoLeft PCPPNativeQueryLoop.machine 5 :=
  CursorRestore.repeat_forward PCPPNativeQueryIteration.machine PCPPNativeQueryLoop.accepted 5 query_iteration

end NearCubicWires.RepairOrdinary.PCPPNativeForward

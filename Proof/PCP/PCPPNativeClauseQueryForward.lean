import Proof.PCP.PCPPNativeClauseForward

/-! The whole cold original substituted-node producer has a forward
output cursor, including resource production, query initialization and
original-oracle scalar parsing. The existing output framer can measure it. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseForward
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem allocate : CursorRestore.NoLeft PCPPNativeQueryAllocate.machine 5 :=
  EquationRowCuts.unselected_forward PCPPNativeQueryReusable.eraseSlots _ 5 (by decide)
theorem query_prepare : CursorRestore.NoLeft PCPPNativeQueryCold.prepare 5 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (CursorRestore.focus_forward PCPPNativeQueryCold.allocateSlots (by decide) _ 5 allocate)
      (EquationRowCuts.unselected_forward PCPPNativeQueryCold.widthSlots _ 5 (by decide)))
    (EquationRowCuts.unselected_forward PCPPNativeQueryCold.countSlots _ 5 (by decide))
theorem query_position : CursorRestore.NoLeft PCPPNativeQueryCold.position 5 := by
  intro q bits a ha
  simp only [PCPPNativeQueryCold.position,DecompositionCountPosition.move] at ha
  split at ha
  · cases ha
    decide
  · contradiction
theorem query_cold : CursorRestore.NoLeft PCPPNativeQueryCold.queryMachine 5 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ query_prepare query_position)
    (CursorRestore.focus_forward PCPPNativeQueryCold.loopSlots PCPPNativeQueryCold.loop_injective _ 5 PCPPNativeForward.query_bank)
theorem resource_query : CursorRestore.NoLeft PCPPNativeResourceQuery.machine 102 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward PCPPNativeResourceQuery.resourceSlots _ 102 (by
      intro i; apply Fin.ne_of_val_ne; change i.val≠102; omega))
    (CursorRestore.focus_forward PCPPNativeResourceQuery.querySlots PCPPNativeResourceQuery.query_injective _ 5 query_cold)
theorem conjunction_start : CursorRestore.NoLeft PCPPNativeConjunctionStart.machine 4 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowRaw.embedded_extra_forward PCPPNativeAddress.machine (0:Fin 1))
    (CursorRestore.focus_forward PCPPNativeConjunctionStart.outputSlot (by decide) _ 0
      (PCPPNativeForward.literal PCPPNativeConjunctionStart.trueBits))
theorem conjunction : CursorRestore.NoLeft PCPPNativeQueryConjunction.machine 102 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.embedded_forward 3 PCPPNativeResourceQuery.machine 102 resource_query)
    (CursorRestore.focus_forward PCPPNativeQueryConjunction.seedSlots PCPPNativeQueryConjunction.seed_injective
      _ 4 conjunction_start)
theorem whole : CursorRestore.NoLeft PCPPNativeClauseOracle.machine 102 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.embedded_forward 85 PCPPNativeQueryConjunction.machine 102 conjunction)
      (EquationRowCuts.unselected_forward PCPPNativeClauseOracle.scalarSlots _ 102 (by decide)))
    (CursorRestore.focus_forward PCPPNativeClauseOracle.clauseSlots PCPPNativeClauseOracle.clause_injective _ 47 raw)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseForward

import Proof.PCP.PCPPNativeForwardScalar

/-! Every executed native node branch appends to the same forward output.
All readers/classifiers are statically disjoint from that output tape. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeForward
open LocalBitMultitape RepairSource.ProjectionNormalization PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem not_node : CursorRestore.NoLeft PCPPNativeNotNode.machine 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ (literal_append PCPPNativeNotNode.firstBits) address)
    (literal_append PCPPNativeNotNode.lastBits)
theorem binary_node (isOr : Bool) : CursorRestore.NoLeft (PCPPNativeBinary.machine isOr) 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.embedded_forward 1 _ 20 (literal_append (PCPPNativeBinary.firstBits isOr)))
      (EquationRowCuts.embedded_forward 1 _ 20 address))
    (CursorRestore.focus_forward PCPPNativeBinary.rightSlots PCPPNativeBinary.right_injective _ 20 address)
theorem input_front (negative : Bool) : CursorRestore.NoLeft (PCPPNativeInput.front negative) 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.embedded_forward 1 _ 20 (literal_append PCPPNativeInput.firstBits))
      (EquationRowCuts.embedded_forward 1 _ 20 sum))
    (EquationRowCuts.embedded_forward 1 _ 20 (literal_append (PCPPNativeInput.betweenBits negative)))
theorem input_target (negative : Bool) : CursorRestore.NoLeft (PCPPNativeInput.targetMachine negative) 20 := by
  cases negative
  · exact EquationRowCuts.embedded_forward 1 _ 20 sum
  · exact CursorRestore.focus_forward PCPPNativeSumBinary.rightSlots PCPPNativeSumBinary.right_injective _ 20 sum
theorem input_node (negative : Bool) : CursorRestore.NoLeft (PCPPNativeInput.machine negative) 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ (input_front negative) (input_target negative))
    (EquationRowCuts.embedded_forward 1 _ 20 (literal_append PCPPNativeInput.lastBits))
theorem query_tail : CursorRestore.NoLeft PCPPNativeQueryTail.machine 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ (literal_append PCPPNativeQueryTail.firstBits) address)
    (literal_append PCPPNativeQueryTail.lastBits)

theorem node_literal (bits : List Bool) : CursorRestore.NoLeft (literalProgram bits) 5 :=
  CursorRestore.focus_forward (fun _ : Fin 1 => (5 : Fin 119)) (by
    intro i j _; exact Subsingleton.elim i j) (HierarchyFixedWord.raw bits) 0 (literal bits)
theorem node_arg (right : Bool) : CursorRestore.NoLeft (argProgram right) 5 :=
  EquationRowCuts.unselected_forward (argSlots right) _ 5 (by cases right <;> decide)
theorem node_value : CursorRestore.NoLeft valueProgram 5 :=
  EquationRowCuts.unselected_forward valueSlots _ 5 (by decide)

theorem node : CursorRestore.NoLeft PCPPNativeNodeMachine.machine 5 := by
  apply EquationCut.calls_forward
  intro j
  fin_cases j
  · exact EquationRowCuts.unselected_forward readSlots _ 5 (by decide)
  · exact EquationRowCuts.unselected_forward (fun _ : Fin 1 => (7 : Fin 119)) _ 5 (by decide)
  · exact node_literal _
  · exact node_literal _
  · exact node_arg false
  · exact CursorRestore.focus_forward (fieldSlots false) (field_injective false) _ 20 not_node
  · exact node_arg false
  · exact node_arg true
  · exact CursorRestore.focus_forward binarySlots binary_injective _ 20 (binary_node false)
  · exact node_arg false
  · exact node_arg true
  · exact CursorRestore.focus_forward binarySlots binary_injective _ 20 (binary_node true)
  · exact EquationRowCuts.unselected_forward lookupSlots _ 5 (by decide)
  · exact EquationRowCuts.unselected_forward (fun _ : Fin 1 => (14 : Fin 119)) _ 5 (by decide)
  · exact node_value
  · exact CursorRestore.focus_forward inputSlots input_injective _ 20 (input_node false)
  · exact node_value
  · exact CursorRestore.focus_forward inputSlots input_injective _ 20 (input_node true)
  · exact EquationRowCuts.unselected_forward (fun _ : Fin 1 => (15 : Fin 119)) _ 5 (by decide)
  · exact node_literal _
  · exact node_literal _

end NearCubicWires.RepairOrdinary.PCPPNativeForward

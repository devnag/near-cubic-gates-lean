import Proof.Amplification.RecoveryTseitinNativeNodeLoop
import Proof.Amplification.RecoveryTseitinForward
import Proof.PCP.PCPPNativeForwardScalar

/-! The original full node CNF stream is append-only on its actual formula
tape, so the existing physical formula framer measures its real output. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_emit_forward (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) :
    CursorRestore.NoLeft (RecoveryTseitinClauseAppend.emitMachine signs sources) 239 :=
  CursorRestore.composition_forward _ _ 239
    (EquationRowRaw.embedded_extra_forward (RecoveryTseitinKernel.kernel signs sources) (0 : Fin 2))
    RecoveryTseitinTautology.append_forward
theorem plans_forward (ps : List RecoveryTseitinNode.Plan) :
    CursorRestore.NoLeft (RecoveryTseitinNode.machine ps) 239 := by
  induction ps with
  | nil=>intro q bs a ha; contradiction
  | cons p ps ih=>exact CursorRestore.composition_forward _ _ _ (node_emit_forward p.signs p.sources) ih
theorem node_program_forward (k : Fin 6) : CursorRestore.NoLeft (NodeController.nodeProgram k) 1333 :=
  CursorRestore.focus_forward (kernelSlots (decide (k=2))) (kernel_injective _) _ 239
    (plans_forward (RecoveryTseitinNode.plans k))
theorem node_controller_forward : CursorRestore.NoLeft NodeController.machine 1333 := by
  apply EquationCut.calls_forward
  intro j
  fin_cases j
  · exact EquationRowCuts.unselected_forward (NodeController.tagSlots false) _ _ (by decide)
  · exact EquationRowCuts.unselected_forward (NodeController.tagSlots true) _ _ (by decide)
  all_goals exact node_program_forward _
theorem cold_node_forward : CursorRestore.NoLeft coldNodeMachine 1333 :=
  CursorRestore.composition_forward _ _ 1333
    (CursorRestore.composition_forward _ _ 1333
      (EquationRowRaw.embedded_extra_forward referencesMachine (234 : Fin 236))
      (EquationRowCuts.unselected_forward kernelBankSlots _ _ (bank_away _ (Or.inr (Or.inr rfl)))))
    node_controller_forward
namespace Reuse
theorem masked_forward : CursorRestore.NoLeft maskedMachine 1333 :=
  PCPPNativeForward.masked coldNodeMachine selected 1333 (by decide) cold_node_forward
theorem prefix_forward : CursorRestore.NoLeft prefixMachine 1333 :=
  EquationRowCuts.embedded_forward 2 maskedMachine 1333 masked_forward
theorem erase_forward : CursorRestore.NoLeft eraseMachine 1333 :=
  EquationRowCuts.unselected_forward eraseSlots _ _ (erase_away _ (Or.inr (Or.inr (Or.inr rfl))))
theorem advance_forward : CursorRestore.NoLeft advanceMachine 1333 :=
  EquationRowCuts.unselected_forward advanceSlots _ _ (by decide)
theorem step_forward : CursorRestore.NoLeft stepMachine 1333 :=
  CursorRestore.composition_forward _ _ 1333
    (CursorRestore.composition_forward _ _ 1333 prefix_forward erase_forward) advance_forward
theorem loop_forward : CursorRestore.NoLeft loopMachine 1333 :=
  CursorRestore.repeat_forward stepMachine (fun _ _=>true) 1333 step_forward

end Reuse
end NearCubicWires.RepairSource.RecoveryTseitinNative

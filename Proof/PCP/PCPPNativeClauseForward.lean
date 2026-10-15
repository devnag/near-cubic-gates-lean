import Proof.PCP.PCPPNativeClauseOracleRun
import Proof.PCP.PCPPNativeForwardQuery

/-! The entire original clause loop only appends to its output. This is
the exact rule-table premise for the existing paid native-output framer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseForward
open LocalBitMultitape RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal (bits : List Bool) : CursorRestore.NoLeft (PCPPNativeClauseBank.literalMachine bits) 20 :=
  CursorRestore.focus_forward PCPPNativeClauseBank.literalSlots (by decide) _ 0 (PCPPNativeForward.literal bits)
theorem sum (a b : Fin 7) (h : a≠b) : CursorRestore.NoLeft (PCPPNativeClauseBank.sumMachine a b) 20 :=
  CursorRestore.focus_forward (PCPPNativeClauseBank.sumSlots a b) (PCPPNativeClauseBank.sum_injective a b h)
    _ 20 PCPPNativeForward.sum
theorem node (tag : ℕ) (a b c d : Fin 7) (hab : a≠b) (hcd : c≠d) :
    CursorRestore.NoLeft (PCPPNativeClauseBank.nodeMachine tag a b c d) 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ (literal _) (sum a b hab)) (sum c d hcd)
theorem block : CursorRestore.NoLeft PCPPNativeClauseBank.machine 20 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ (node 4 0 1 0 2 (by decide) (by decide))
      (node 4 0 4 0 3 (by decide) (by decide))) (node 3 0 5 6 4 (by decide) (by decide))
theorem body : CursorRestore.NoLeft PCPPNativeClauseBody.machine 47 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward PCPPNativeClauseBody.tripleSlots _ 47 (by
      intro i; apply Fin.ne_of_val_ne; change i.val≠47; omega))
    (CursorRestore.focus_forward PCPPNativeClauseBody.blockSlots PCPPNativeClauseBody.block_injective _ 20 block)
theorem reusable : CursorRestore.NoLeft PCPPNativeClauseReuse.machine 47 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _ body
      (EquationRowCuts.unselected_forward PCPPNativeClauseReuse.counterSlots _ 47 (by decide)))
    (EquationRowCuts.unselected_forward PCPPNativeClauseReuse.eraseSlots _ 47 (by decide))
theorem loop : CursorRestore.NoLeft PCPPNativeClauseLoop.machine 47 :=
  CursorRestore.repeat_forward PCPPNativeClauseReuse.machine (fun _ _=>true) 47 reusable
theorem raw : CursorRestore.NoLeft PCPPNativeClauseRawRun.machine 47 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward PCPPNativeClauseDriverEntry.slots _ 47 (by decide))
    (CursorRestore.focus_forward PCPPNativeClauseRawRun.slots PCPPNativeClauseRawRun.slots_injective _ 47 loop)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseForward

import Proof.Amplification.RecoveryTseitinColdStream
import Proof.Supplier.EquationRowForward

/-! The actual cold tautology output is append-only. The enclosing formula
framer can therefore record its physical cursor without a second length input. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem append_forward : CursorRestore.NoLeft appendMachine 239 := by
  apply CursorRestore.focus_forward
    (CompetitorFieldEmit.slots (RecoveryTseitinKernel.clauseSlot.castAdd 2) 239 240)
    (CompetitorFieldEmit.slots_injective _ _ _ (by decide) (by decide) (by decide))
    CompetitorFrameAppend.machine 1
  intro q bs a ha
  fin_cases q <;> simp [CompetitorFrameAppend.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> simp [CompetitorFrameAppend.action])
    | (cases ha; simp [CompetitorFrameAppend.action])

theorem emit_forward : CursorRestore.NoLeft emitMachine 239 :=
  CursorRestore.composition_forward _ _ 239
    (EquationRowRaw.embedded_extra_forward machine (0 : Fin 2)) append_forward
theorem body_forward : CursorRestore.NoLeft bodyMachine 239 :=
  CursorRestore.composition_forward _ _ 239 emit_forward
    (EquationRowCuts.unselected_forward incrementSlots _ 239 (by decide))
theorem loop_forward : CursorRestore.NoLeft loopMachine 239 :=
  CursorRestore.repeat_forward bodyMachine (fun _ _=>true) 239 body_forward

namespace Cold
theorem bank_forward : CursorRestore.NoLeft bankMachine 239 :=
  EquationRowCuts.unselected_forward slots _ 239 (by
    intro j he
    have h:=congrArg Fin.val he
    rw [slots_value] at h
    split_ifs at h <;> omega)
theorem enter_forward : CursorRestore.NoLeft enter 239 := by
  intro q bs a ha
  dsimp only [enter] at ha
  split at ha
  · cases ha
    decide
  · contradiction
theorem prepared_forward : CursorRestore.NoLeft preparedMachine 239 :=
  CursorRestore.composition_forward _ _ 239
    (CursorRestore.composition_forward _ _ 239 bank_forward enter_forward) loop_forward
theorem drivers_forward : CursorRestore.NoLeft driversMachine 239 := by
  apply CursorRestore.composition_forward
  · apply EquationRowCuts.unselected_forward powerSlots _ 239
    intro j he
    have h:=congrArg Fin.val he
    dsimp only [powerSlots] at h
    split_ifs at h <;> dsimp at h <;> omega
  · exact EquationRowCuts.unselected_forward countSlots _ 239 (by decide)
theorem output_forward : CursorRestore.NoLeft machine 239 :=
  CursorRestore.composition_forward _ _ 239 drivers_forward
    (CursorRestore.focus_forward streamSlots stream_injective preparedMachine 239 prepared_forward)

end Cold
end NearCubicWires.RepairSource.RecoveryTseitinTautology

import Proof.Amplification.RecoveryPCPFormulaResumePrefix
import Proof.PCP.PCPPNativeForwardScalar

/-! The original all-randomness producer keeps its formula cursor forward
through every source rewind, scratch erasure and randomness increment. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeForward
open LocalBitMultitape RepairOrdinary RecoveryExecution SourceInterfaces ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_append : CursorRestore.NoLeft CompetitorFrameAppend.machine 1 := by
  intro q bits a ha
  fin_cases q <;> cases hb : bits 0 <;> cases hc : bits 2 <;>
    simp [CompetitorFrameAppend.machine,hb,hc] at ha
  all_goals cases ha; decide

theorem clause_append : CursorRestore.NoLeft RecoverySourceClauseReuse.appendMachine 276 :=
  CursorRestore.focus_forward (CompetitorFieldEmit.slots (262 : Fin 280) 276 277) (by decide)
    CompetitorFrameAppend.machine 1 field_append

theorem clause : CursorRestore.NoLeft RecoverySourceClauseReuse.machine 276 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · exact EquationRowCuts.unselected_forward RecoverySourceClauseReuse.nativeSlots _ 276 (by
        intro j; apply Fin.ne_of_val_ne; change j.val≠276; have hi:=j.isLt; omega)
    · exact clause_append
  · exact EquationRowCuts.unselected_forward RecoverySourceClauseReuse.eraseSlots _ 276 (by decide)

theorem clauses : CursorRestore.NoLeft RecoverySourceClauseList.machine 276 :=
  CursorRestore.repeat_forward RecoverySourceClauseReuse.machine (fun _ _=>true) 276 clause

theorem address_away (j : Fin 37) : RecoveryPCPFormulaResumeRow.addressSlots j≠(276 : Fin 317) := by
  apply Fin.ne_of_val_ne
  have hj:=j.isLt
  dsimp [RecoveryPCPFormulaResumeRow.addressSlots]
  split_ifs <;> omega

theorem row : CursorRestore.NoLeft RecoveryPCPFormulaResumeRow.machine 276 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward RecoveryPCPFormulaResumeRow.addressSlots _ 276 address_away)
    (CursorRestore.focus_forward RecoveryPCPFormulaResumeRow.clauseSlots RecoveryPCPFormulaResumeRow.clause_injective
      RecoverySourceClauseList.machine 276 clauses)

theorem reset : CursorRestore.NoLeft RecoveryPCPFormulaResumeRowReset.machine 276 :=
  PCPPNativeForward.masked RecoveryPCPFormulaResumeRow.machine RecoveryPCPFormulaResumeRowReset.selected
    276 (by decide) row

theorem reusable : CursorRestore.NoLeft RecoveryPCPFormulaResumeRowReusable.machine 276 :=
  CursorRestore.composition_forward _ _ _ reset
    (EquationRowCuts.unselected_forward RecoveryPCPFormulaResumeRowReusable.slots _ 276 (by decide))

theorem advance : CursorRestore.NoLeft RecoveryPCPFormulaResumeRowRandomness.machine 276 :=
  EquationRowCuts.unselected_forward RecoveryPCPFormulaResumeRowRandomness.slots _ 276 (by
    intro j h
    apply address_away j
    exact Fin.ext (congrArg (fun i : Fin 318=>i.val) h))

theorem body : CursorRestore.NoLeft RecoveryPCPFormulaResumeRows.bodyMachine 276 :=
  CursorRestore.composition_forward _ _ _ reusable advance

theorem loop : CursorRestore.NoLeft RecoveryPCPFormulaResumeRows.loopMachine 276 :=
  CursorRestore.repeat_forward RecoveryPCPFormulaResumeRows.bodyMachine (fun _ _=>true) 276 body

theorem rows : CursorRestore.NoLeft RecoveryPCPFormulaResumeRows.machine 276 :=
  CursorRestore.composition_forward _ _ _ loop
    (CursorRestore.focus_forward RecoveryPCPFormulaResumeRows.tailSlots RecoveryPCPFormulaResumeRows.tail_injective
      RecoveryPCPFormulaResumeRowReusable.machine 276 reusable)

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeForward

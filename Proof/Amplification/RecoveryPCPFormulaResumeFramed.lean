import Proof.Amplification.RecoveryPCPFormulaResumePosition
import Proof.Amplification.RecoveryTseitinForward
import Proof.Assembly.AppendOutputFrame

/-! Measure the actual complete formula append cursor, execute its rewind,
and frame those same emitted bytes for the existing balanced serializer. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem forward : CursorRestore.NoLeft machine 276 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.focus_forward prefixSlots prefix_injective RecoveryTseitinTautology.Cold.machine
      239 RecoveryTseitinTautology.Cold.output_forward)
    (CursorRestore.focus_forward rowSlots row_injective RecoveryPCPFormulaResumeRows.machine
      276 RecoveryPCPFormulaResumeForward.rows)

theorem raw_forward : CursorRestore.NoLeft rawMachine 276 :=
  CursorRestore.composition_forward _ _ _ position_forward forward

noncomputable def framedMachine := AppendOutputFrame.machine rawMachine (276 : Fin 580)
noncomputable def framedInput (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) :=
  AppendOutputFrame.input (input p R Q cap logCap resetCap)
def framedBudget (cap R Q count length : Nat) := 2*rawBudget cap R Q count+4*length+7

theorem framed_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (cap logCap resetCap : Nat)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    run framedMachine (framedBudget cap R Q (Codec.clauses p).length
        (FieldList.stream (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length)
      (framedInput p R Q cap logCap resetCap)=some r ∧
      r.final.tapes 582=frame (FieldList.stream
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)) ∧
      (∀ i,r.final.heads i=0) ∧
      r.steps≤framedBudget cap R Q (Codec.clauses p).length
        (FieldList.stream (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length := by
  obtain ⟨base,hbase,bt,bh,bs⟩ := raw_run p R Q hr hq x cap logCap resetCap hc hl hz
  obtain ⟨r,hrun,rt,rh,rs⟩ := AppendOutputFrame.frame_run rawMachine 276 raw_forward _ _ base hbase _ bt bh
  have hb : 2*base.steps+4*(FieldList.stream
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length+7≤
      framedBudget cap R Q (Codec.clauses p).length (FieldList.stream
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length := by
    unfold framedBudget; omega
  have hmore:=run_moreFuel framedMachine _
    (framedBudget cap R Q (Codec.clauses p).length (FieldList.stream
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length-
      (2*base.steps+4*(FieldList.stream
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length+7)) _ r hrun
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨r,hmore,rt,rh,rs.trans hb⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix

import Proof.Amplification.RecoveryPCPFormulaResumeEntry

/-! The exact ten-data-tape ordinary entry produces the original balanced
PCP recovery formula. No false workspace, reset budget or execution premise
is required at entry; the same physical machine writes its own working cells. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ r,
    run machine (budget (RecoverySourceClauseLoad.uniformBudget Q R) R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      (entryData p R Q (RecoverySourceClauseLoad.uniformBudget Q R))=some r ∧
      r.final.tapes 714=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      r.steps≤budget (RecoverySourceClauseLoad.uniformBudget Q R) R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  let cap:=RecoverySourceClauseLoad.uniformBudget Q R
  let logCap:=RecoveryProjectionRowsRewind.batchBudget R Q+2
  let resetCap:=RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length
  obtain ⟨base,hbase,bt,bs⟩ := sparse_run p R Q hr hq x cap logCap resetCap (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  rw [sparse_entry] at hbase
  let caps : Fin 716→Nat := fun i=>(entryData p R Q cap i).length
  have hin : ZeroPadding.config caps (initialConfiguration machine (fun i=>omitBlank (entryData p R Q cap i)))=
      initialConfiguration machine (entryData p R Q cap) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      exact pad_omitBlank _
  obtain ⟨r,hrun,rf,rs,_rp⟩ := ZeroPadding.run_config machine caps _ _ base hbase
  rw [hin] at hrun
  refine ⟨r,hrun,?_,rs.trans_le bs⟩
  rw [rf]
  change ZeroPadding.pad 0 (base.final.tapes 714)=_
  rw [ZeroPadding.pad_zero,bt]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize

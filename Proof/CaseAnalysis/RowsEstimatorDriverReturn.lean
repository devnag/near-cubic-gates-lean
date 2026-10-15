import Proof.CaseAnalysis.RowsEstimatorDriverSweep

/-! The original saturating return reuses its existing D+1 false backing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem return_padded (source : List Bool) (D pos : ℕ) : ∃ r,
    runFrom CompetitorRecordRewind.machine (2*D+2)
      (CompetitorRecordRewind.cfg 0 source pos D 0 0 (List.replicate (D+1) false))=some r ∧
      r.final=CompetitorRecordRewind.cfg 2 source (pos-D) D 0 0 (List.replicate (D+1) false) ∧
      r.steps=2*D+2 := by
  obtain ⟨base,hb,bf,bs⟩ := return_partial source D pos
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config CompetitorRecordRewind.machine
    (![0,0,D+1] : Fin 3 → ℕ) _ _ base hb
  have hin : ZeroPadding.config (![0,0,D+1] : Fin 3 → ℕ)
      (CompetitorRecordRewind.cfg 0 source pos D 0 0 [])=
      CompetitorRecordRewind.cfg 0 source pos D 0 0 (List.replicate (D+1) false) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,CompetitorRecordRewind.cfg,ZeroPadding.pad]
  rw [hin] at hr
  refine ⟨r,hr,?_,rs.trans bs⟩
  rw [rf,bf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i;fin_cases i <;> simp [ZeroPadding.config,CompetitorRecordRewind.cfg,ZeroPadding.pad,List.replicate_add]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep

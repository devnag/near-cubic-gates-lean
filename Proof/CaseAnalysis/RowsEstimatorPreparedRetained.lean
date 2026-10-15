import Proof.CaseAnalysis.RowsEstimatorPreparedRun
import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmRetained

/-! Native cut bytes and the original C word survive the paid preparation too. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepare_readonly (p : Program) (i : Fin (WholePrefix.tapes p)) (hi : i.val=52 ∨ i.val=68) :
    NoWrite (WarmPrepare.machine p) (WarmPrepare.old p i) := by
  apply composition
  · apply unselected
    apply WarmPrepare.pad_avoids p _
    exact hi.elim Or.inl (fun h=>Or.inr (Or.inl h))
  · apply unselected
    apply WarmPrepare.copy_avoids_old
    intro j he
    have hv:=congrArg (fun z : Fin (WholePrefix.tapes p)=>z.val) he
    rw [WarmFields.slots_val] at hv
    fin_cases j <;> simp at hv <;> omega

theorem protected_readonly (a : WilliamsAlgorithm) (i : Fin (WholePrefix.tapes (producer a)))
    (hi : i.val=52 ∨ i.val=68) : NoWrite (machine a) (WarmPrepare.old (producer a) i) := by
  apply composition
  · exact prepare_readonly (producer a) i hi
  · exact embedded 7 (WarmActual.machine a) (Reuse.old (producer a) i)
      (WarmActual.protected_readonly a i hi)

theorem protected_run (a : WilliamsAlgorithm) (i : Fin (WholePrefix.tapes (producer a)))
    (hi : i.val=52 ∨ i.val=68) (fuel : ℕ) (start : Configuration _ _) (r : ExecutionReceipt _ _)
    (hr : runFrom (machine a) fuel start=some r) :
    r.final.tapes (WarmPrepare.old (producer a) i)=start.tapes (WarmPrepare.old (producer a) i) :=
  run_tape (machine a) _ (protected_readonly a i hi) fuel start r hr

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared

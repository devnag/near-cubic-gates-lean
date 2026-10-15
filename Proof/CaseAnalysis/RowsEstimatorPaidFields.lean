import Proof.CaseAnalysis.RowsEstimatorPaidLayout

/-! Only the physical D word changes in the consumer bank during allocation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem old_driver_ne (p : Program) (i : Fin (WholePrefix.tapes p)) :
    WarmPrepare.old p i≠WarmPrepare.driver p := by
  intro he
  have hv:=congrArg (fun z : Fin (WarmPrepare.tapes p)=>z.val) he
  rw [WarmPrepare.old_val,WarmPrepare.driver_val] at hv
  have h:=i.isLt
  omega
theorem log_driver_ne (p : Program) : WarmPrepare.log p≠WarmPrepare.driver p := by
  intro he
  have hv:=congrArg (fun z : Fin (WarmPrepare.tapes p)=>z.val) he
  rw [WarmPrepare.log_val,WarmPrepare.driver_val] at hv
  omega
theorem source_driver_ne (p : Program) (i : Fin 7) :
    WarmPrepare.source p i≠WarmPrepare.driver p := by
  intro he
  have hv:=congrArg (fun z : Fin (WarmPrepare.tapes p)=>z.val) he
  rw [WarmPrepare.source_val,WarmPrepare.driver_val] at hv
  unfold Reuse.tapes at hv
  omega

theorem data_D (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) :
    Function.update (WarmPrepare.data p A 0 L fields) (WarmPrepare.driver p) (List.replicate D true)=
      WarmPrepare.data p A D L fields := by
  apply WarmPrepare.data_ext p
  · intro i
    rw [Function.update_of_ne (old_driver_ne p i),WarmPrepare.at_old,WarmPrepare.at_old]
  · rw [Function.update_of_ne (log_driver_ne p),WarmPrepare.at_log,WarmPrepare.at_log]
  · rw [Function.update_of_ne (Ne.symm (WarmPrepared.driver_ne p)),WarmPrepare.at_spare,WarmPrepare.at_spare]
  · rw [Function.update_self,WarmPrepare.at_driver]
  · intro i
    rw [Function.update_of_ne (source_driver_ne p i),WarmPrepare.at_source,WarmPrepare.at_source]

theorem live_D (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) :
    Function.update (WarmPrepare.live p (WarmPrepare.data p A 0 L fields) out)
      (WarmPrepare.driver p) (List.replicate D true)=
      WarmPrepare.live p (WarmPrepare.data p A D L fields) out := by
  unfold WarmPrepare.live
  rw [Function.update_comm (Ne.symm (WarmPrepared.driver_ne p)),data_D]

theorem bare_old (p : Program) (row : EquationRow.Input) (C : ℕ) (i : Fin 70) :
    WarmFields.bare p row C (i.castAdd (CloseoutRowsRawRecord.tapes p))=Scanned.output row C i := by
  simp only [WarmFields.bare,Warm.supplied,Fin.addCases_left]

theorem input_old (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) (i : Fin 70) :
    ScannedClean.input a row C (ScannedClean.old a (i.castAdd (DriverLayout.tapes a)))=Scanned.output row C i := by
  simp only [ScannedClean.input,ScannedClean.old,ScannedDriver.input,Fin.addCases_left]

theorem input_blank (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (i : Fin (ScannedClean.tapes a)) (hi : 70 ≤ i.val) : ScannedClean.input a row C i=[] := by
  revert hi
  refine Fin.addCases (m:=ScannedDriver.tapes a) (n:=3) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=70) (n:=DriverLayout.tapes a) (fun k=>?_) (fun k=>?_) j
    · intro hi
      have hk:=k.isLt
      simp only [Fin.val_castAdd] at hi
      omega
    · intro _
      simp only [ScannedClean.input,ScannedDriver.input,Fin.addCases_left,Fin.addCases_right]
  · intro _
    simp only [ScannedClean.input,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

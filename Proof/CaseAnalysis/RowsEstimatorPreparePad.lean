import Proof.CaseAnalysis.RowsEstimatorPrepareWords

/-! Physical padding of every owned Warm word, with all source fields retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_input (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) (i : Fin (WholePrefix.tapes p-2+1+1)) :
    data p A D 0 fields (padSlots p i)=Pad.input (owned p A) D i := by
  refine Fin.addCases (m:=WholePrefix.tapes p-2+1) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=WholePrefix.tapes p-2) (n:=1) (fun k=>?_) (fun k=>?_) j
    · simp only [pad_work,at_work,Pad.input,Fin.addCases_left]
    · simp only [pad_driver,at_driver,Pad.input,Fin.addCases_left,Fin.addCases_right]
  · simp only [pad_log,at_log,Pad.input,Fin.addCases_right,List.replicate_zero]

theorem pad_output (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) :
    install (padSlots p) (data p A D 0 fields) (Pad.output (owned p A) D)=
      data p (WarmReuse.padded p D A) D (D+1) fields := by
  apply data_ext p
  · intro i
    by_cases h52 : i.val=52
    · rw [install_other _ _ _ _ (pad_avoids p _ (Or.inl h52)),at_old,at_old]
      simp only [WarmReuse.padded,Reset.caps,h52,true_or,ite_true,ZeroPadding.pad_zero]
    · by_cases h68 : i.val=68
      · rw [install_other _ _ _ _ (pad_avoids p _ (Or.inr (Or.inl h68))),at_old,at_old]
        simp only [WarmReuse.padded,Reset.caps,h68,or_true,ite_true,ZeroPadding.pad_zero]
      · obtain ⟨j,hj⟩:=cover p i h52 h68
        rw [←hj,←pad_work,install_slot _ (pad_injective p)]
        simp only [Pad.output,Fin.addCases_left,pad_work,at_work,owned_pad]
  · rw [←pad_log p 0,install_slot _ (pad_injective p)]
    simp only [Pad.output,Fin.addCases_right,pad_log,at_log]
  · rw [install_other _ _ _ _ (pad_avoids p _ (Or.inr (Or.inr (Or.inl rfl)))),at_spare,at_spare]
  · rw [←pad_driver p 0,install_slot _ (pad_injective p)]
    simp only [Pad.output,Fin.addCases_left,Fin.addCases_right,pad_driver,at_driver]
  · intro i
    rw [install_other _ _ _ _ (pad_avoids p _ (Or.inr (Or.inr (Or.inr (by rw [source_val];omega))))),at_source,at_source]

theorem pad_ready (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ)
    (fields : Fin 7 → List Bool) :
    ReadyRun (pad p) (2*D+4) (data p A D 0 fields)
      (data p (WarmReuse.padded p D A) D (D+1) fields) := by
  have h:=(Pad.ready (owned p A) D).focus (padSlots p) (pad_injective p)
    (data p A D 0 fields) (pad_input p A D fields)
  rw [pad_output] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare

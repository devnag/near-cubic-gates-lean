import Proof.CaseAnalysis.RowsEstimatorScannedCleanRun
import Proof.CaseAnalysis.RowsEstimatorPreparedPorts

/-! The actual driver aliases its preserved70 words and D output into the
consumer bank. Every other driver word has a disjoint private port. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) (p : Program):=WarmPrepare.tapes p+ScannedClean.tapes a
noncomputable def old (a : WilliamsAlgorithm) (p : Program) (i : Fin (WarmPrepare.tapes p)) : Fin (tapes a p):=
  i.castAdd (ScannedClean.tapes a)
noncomputable def slots (a : WilliamsAlgorithm) (p : Program) (i : Fin (ScannedClean.tapes a)) : Fin (tapes a p):=
  if h:i.val<70 then ⟨i.val,by dsimp [tapes,WarmPrepare.tapes,Reuse.tapes,WholePrefix.tapes];omega⟩
  else if i=ScannedClean.driver a then old a p (WarmPrepare.driver p)
  else i.natAdd (WarmPrepare.tapes p)

theorem driver_large (a : WilliamsAlgorithm) : 70 ≤ (ScannedClean.driver a).val := by
  change 70 ≤ (ScannedDriver.driver a).val
  rw [ScannedDriver.driver_val]
  omega

theorem at_driver (a : WilliamsAlgorithm) (p : Program) :
    slots a p (ScannedClean.driver a)=old a p (WarmPrepare.driver p) := by
  simp only [slots,show ¬(ScannedClean.driver a).val<70 by have h:=driver_large a;omega,ite_true,dite_false]

theorem at_old (a : WilliamsAlgorithm) (p : Program) (i : Fin 70) :
    slots a p (ScannedClean.old a (i.castAdd (DriverLayout.tapes a)))=
      old a p (WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p))) := by
  have hi : (ScannedClean.old a (i.castAdd (DriverLayout.tapes a))).val<70:=i.isLt
  simp only [slots,hi,dif_pos]
  rfl

theorem injective (a : WilliamsAlgorithm) (p : Program) : Function.Injective (slots a p) := by
  intro i j he
  have hv:=congrArg (fun z : Fin (tapes a p)=>z.val) he
  have hd : 70 ≤ (WarmPrepare.driver p).val := by
    rw [WarmPrepare.driver_val]
    unfold WholePrefix.tapes
    omega
  have ht : (WarmPrepare.driver p).val<WarmPrepare.tapes p:=(WarmPrepare.driver p).isLt
  unfold slots at hv
  split_ifs at hv with hi hid hj hjd hj hjd
  all_goals try {subst i;subst j;rfl}
  all_goals first
  | exact Fin.ext (by simpa only [old,Fin.val_castAdd,Fin.val_natAdd] using hv)
  | (simp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv;omega)

theorem avoids_old (a : WilliamsAlgorithm) (p : Program) (i : Fin (WarmPrepare.tapes p))
    (hi : 70 ≤ i.val) (hd : i≠WarmPrepare.driver p) : ∀ j,slots a p j≠old a p i := by
  intro j he
  have hv:=congrArg (fun z : Fin (tapes a p)=>z.val) he
  unfold slots at hv
  split_ifs at hv with hj hjd
  · simp only [old,Fin.val_castAdd] at hv
    omega
  · apply hd
    apply Fin.ext
    simpa only [old,Fin.val_castAdd] using hv.symm
  · simp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    have h:=i.isLt
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

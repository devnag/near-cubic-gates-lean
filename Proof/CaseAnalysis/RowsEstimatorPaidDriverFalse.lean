import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidColdRun
import Proof.CaseAnalysis.RowsEstimatorScannedCleanFalse

/-! The actual aliased driver leaves only its explicitly retained D copy nonzero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem private_slot (a : WilliamsAlgorithm) (p : Program) (i : Fin (ScannedClean.tapes a))
    (h70 : 70 ≤ i.val) (hd : i≠ScannedClean.driver a) :
    slots a p i=i.natAdd (WarmPrepare.tapes p) := by
  simp only [slots,show ¬i.val<70 by omega,hd,dite_false,ite_false]

theorem private_unused (a : WilliamsAlgorithm) (p : Program) (i : Fin (ScannedClean.tapes a))
    (hi : i.val<70 ∨ i=ScannedClean.driver a) : ∀ j,slots a p j≠i.natAdd (WarmPrepare.tapes p) := by
  intro j he
  have hv:=congrArg (fun z : Fin (tapes a p)=>z.val) he
  unfold slots at hv
  split_ifs at hv with hj hd
  · have hN : 70 ≤ WarmPrepare.tapes p:=by
      unfold WarmPrepare.tapes Reuse.tapes WholePrefix.tapes;omega
    simp only [Fin.val_natAdd] at hv
    omega
  · have h:=(WarmPrepare.driver p).isLt
    simp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · have heq : j=i:=Fin.ext (by simp only [Fin.val_natAdd] at hv;omega)
    subst j
    exact hi.elim hj hd

theorem driver_private (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (r : ExecutionReceipt _ _)
    (hr : runFrom (driver a) (ScannedClean.budget a row C) (driverEntry a row C fields out)=some r)
    (i : Fin (ScannedClean.tapes a)) (hi : i≠ScannedClean.fresh a 1) :
    ∃ n,r.final.tapes (i.natAdd (WarmPrepare.tapes (producer a)))=List.replicate n false := by
  obtain ⟨localOut,ready,_old,_d,hzero,_dcopy,hlog,hwork⟩:=ScannedClean.ready a row C
  obtain ⟨base,hb,bt,_bh,_bs⟩:=ready
  obtain ⟨actual,ha,_rc,_rs,_rh,rt,keep⟩:=RecoveryFocus.dock (slots a (producer a)) (injective a (producer a))
    (ScannedClean.machine a) _ (heads a (producer a) out) (input a (producer a) row C fields out)
    (initialConfiguration (ScannedClean.machine a) (ScannedClean.input a row C))
    (slot_heads a (producer a) out) (projected a (producer a) row C fields out) base hb
  have same : actual=r:=Option.some.inj (ha.symm.trans hr)
  subst actual
  by_cases h70 : i.val<70
  · refine ⟨0,?_⟩
    rw [(keep _ (private_unused a (producer a) i (Or.inl h70))).2]
    simp only [input,Fin.addCases_right,List.replicate_zero]
  · by_cases hd : i=ScannedClean.driver a
    · refine ⟨0,?_⟩
      rw [(keep _ (private_unused a (producer a) i (Or.inr hd))).2]
      simp only [input,Fin.addCases_right,List.replicate_zero]
    · obtain ⟨n,hn⟩:=ScannedClean.private_false a _ _ localOut hzero hlog hwork i (by omega) hd hi
      refine ⟨n,?_⟩
      rw [←private_slot a (producer a) i (by omega) hd,rt,bt,hn]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

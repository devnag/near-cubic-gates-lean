import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidOwnedWarmJoin

/-! Actual retirement and the mandatory scanner preserve complete ownership. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem retire_owned_join {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C D fuel bound : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) (worker : Machine (tapes a p) s)
    (initial : Configuration (tapes a p) s)
    (hr : WarmOwned a p worker fuel bound initial row C D word fields) :
    Owned a p (Composition.machine worker (retire a p)) (fuel+1+(2*D+4))
      (bound+1+(2*D+4)) (Composition.leftConfig 5 initial) row C D word fields := by
  obtain ⟨A,extra,x,hx,xh,xt,xs,props,xd,priv,protectedWords⟩:=hr
  obtain ⟨y,hy,yh,yt,ys⟩:=retire_run a p D word A extra props.2.2.1 xd
  have hc : Composition.restart x.final (retire a p).start=
      (⟨DriverRetire.machine.start,heads a p word,Fin.addCases A extra⟩ : Configuration (tapes a p) 5) :=
    restart_state x.final _ _ _ xh xt
  rw [←hc] at hy
  have hj:=Composition.run_join worker (retire a p) _ _ _ x y hx hy
  refine ⟨A,extra,Composition.joinedReceipt x y,hj,yh,yt,?_,props,priv,protectedWords⟩
  change x.steps+1+y.steps ≤ bound+1+(2*D+4)
  omega

theorem cold_owned_join {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input)
    (C D fuel bound : ℕ) (out word : List Bool) (fields : Fin 7 → List Bool)
    (worker : Machine (tapes a p) s) (initial : Configuration (tapes a p) s)
    (he : initial=⟨worker.start,heads a p out,input a p row C fields out⟩)
    (hC : (Header.stream row).length ≤ C)
    (hr : Owned a p worker fuel bound initial row C D word fields) :
    Owned a p (Composition.machine (scanner a p) worker) (Scanned.budget row C+1+fuel)
      (Scanned.budget row C+1+bound) (prefixEntry worker (scanEntry a p row C fields out)) row C D word fields := by
  obtain ⟨x,hx,xh,xt,xs⟩:=scan_run a p row C fields out hC
  obtain ⟨A,extra,y,hy,yh,yt,ys,props,priv,protectedWords⟩:=hr
  have hc : Composition.restart x.final worker.start=initial := by
    rw [he]
    exact restart_state x.final _ _ _ xh xt
  rw [←hc] at hy
  have hj:=Composition.run_join (scanner a p) worker _ _ _ x y hx hy
  refine ⟨A,extra,Composition.joinedReceipt x y,hj,yh,yt,?_,props,priv,protectedWords⟩
  change x.steps+1+y.steps ≤ Scanned.budget row C+1+bound
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

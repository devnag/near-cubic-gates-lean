import Proof.CaseAnalysis.RowsEstimatorPaidRetireJoin

/-! Close the mandatory original scanner around the complete paid estimator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixEntry {n s t : ℕ} (_worker : Machine n t) (source : Configuration n s) :=
  Composition.leftConfig t source

theorem cold_join {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input)
    (C D fuel bound : ℕ) (out word : List Bool) (fields : Fin 7 → List Bool)
    (worker : Machine (tapes a p) s) (initial : Configuration (tapes a p) s)
    (he : initial=⟨worker.start,heads a p out,input a p row C fields out⟩)
    (hC : (Header.stream row).length ≤ C)
    (hr : RetiredJoined a p worker fuel bound initial D word fields) :
    RetiredJoined a p (Composition.machine (scanner a p) worker) (Scanned.budget row C+1+fuel)
      (Scanned.budget row C+1+bound) (prefixEntry worker (scanEntry a p row C fields out)) D word fields := by
  obtain ⟨x,hx,xh,xt,xs⟩:=scan_run a p row C fields out hC
  obtain ⟨A,extra,y,hy,yh,yt,ys,props,xd⟩:=hr
  have hc : Composition.restart x.final worker.start=initial := by
    rw [he]
    exact restart_state x.final _ _ _ xh xt
  rw [←hc] at hy
  have hj:=Composition.run_join (scanner a p) worker _ _ _ x y hx hy
  refine ⟨A,extra,Composition.joinedReceipt x y,hj,yh,yt,?_,props,xd⟩
  change x.steps+1+y.steps ≤ Scanned.budget row C+1+bound
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

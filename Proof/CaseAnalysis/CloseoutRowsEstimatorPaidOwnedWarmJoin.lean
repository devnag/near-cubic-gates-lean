import Proof.CaseAnalysis.RowsEstimatorPaidOwnedTypes

/-! Symbolic finite-control join carries all actual ownership facts. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem warm_owned_join {s t : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input)
    (C D b fp fq : ℕ) (fields : Fin 7 → List Bool) (out word : List Bool)
    (first : Machine (tapes a p) s) (initial : Configuration (tapes a p) s)
    (worker : Machine (WarmPrepare.tapes p) t) (source : Configuration (WarmPrepare.tapes p) t)
    (hp : DriverResult a p first fp initial row C D fields out)
    (he : source=⟨worker.start,WarmPrepare.heads p out,publicInput p row C D fields out⟩)
    (hq : WarmPrepared.Result p worker fq source D b out word fields)
    (hpriv : ∀ extra r,runFrom first fp initial=some r →
      r.final.tapes=Fin.addCases (publicInput p row C D fields out) extra → Private a extra)
    (hprotected : ∀ r,runFrom worker fq source=some r → Protected p row C r.final.tapes) :
    WarmOwned a p (Composition.machine first (TapeEmbedding.machine (ScannedClean.tapes a) worker))
      (fp+1+fq) (fp+1+(8*D+40*b+74)) (Composition.leftConfig t initial) row C D (out++word) fields := by
  obtain ⟨extra,x,hx,xh,xt,xs,xd⟩:=hp
  obtain ⟨y,hy,ys,yh,yt,yw,yd,yl,yfields⟩:=hq
  let z:=TapeEmbedding.receipt (fun _ : Fin (ScannedClean.tapes a)=>0) extra y
  have hz:=TapeEmbedding.run_embed worker (fun _ : Fin (ScannedClean.tapes a)=>0) extra _ _ y hy
  have hc : Composition.restart x.final (TapeEmbedding.machine (ScannedClean.tapes a) worker).start=
      TapeEmbedding.config (fun _ : Fin (ScannedClean.tapes a)=>0) extra source := by
    rw [he]
    rw [heads_eq] at xh
    exact restart_embed x.final worker _ _ extra xh xt
  rw [←hc] at hz
  have hr:=Composition.run_join first (TapeEmbedding.machine (ScannedClean.tapes a) worker) _ _ _ x z hx hz
  refine ⟨y.final.tapes,extra,Composition.joinedReceipt x z,hr,?_,rfl,?_,⟨yt,yw,yd,yl,yfields⟩,xd,hpriv extra x hx xt,hprotected y hy⟩
  · change Fin.addCases y.final.heads (fun _ : Fin (ScannedClean.tapes a)=>0)=heads a p (out++word)
    rw [yh]
    rfl
  · change x.steps+1+y.steps ≤ fp+1+(8*D+40*b+74)
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

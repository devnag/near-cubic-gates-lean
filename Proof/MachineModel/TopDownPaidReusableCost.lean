import Proof.MachineModel.TopDownPaidReusableFamily

/-! The shared capacity gives a uniform linear transaction budget. The
Williams table cost occurs only inside S, never multiplied by itself. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open P1TopDownPaidPayload (tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer machine

theorem uniform_budget (a : WilliamsAlgorithm) (B R S : Nat) (d : Datum)
    (h : Valid a B R S d) : d.budget a B S≤(3*tapes a+6)*(S+1) := by
  have hs:=h.workspace
  have hd : Driver.value a d.row.d d.row.p d.row.cuts.length d.C≤S := by
    unfold P1TopDownPaidReloadCore.budget RawRowJoin.budget P1TopDownPaidReloadCore.fuel
      P1TopDownPaidRetiredPayload.fuel at hs
    omega
  exact P1TopDownPaidReusableBody.budget_le _ _ S
    (fun i=>(input_bound a d.row d.C d.Q d.select h.capacity h.precision i).trans hd) h.workspace

theorem hrow_uniform (a : WilliamsAlgorithm) (ds : List Datum) (dflt : Datum) (S R B : Nat)
    (hv : ∀ k (hk : k<ds.length),Valid a B R S ds[k])
    (k : Nat) (hk : k<ds.length) (out : List Bool) :
    ∃ r,runFrom (machine a) ((3*tapes a+6)*(S+1)) (source a ds S R B k out)=some r ∧
      r.final.heads=(source a ds S R B (k+1) (out++(ds.getD k dflt).emit)).heads ∧
      r.final.tapes=(source a ds S R B (k+1) (out++(ds.getD k dflt).emit)).tapes ∧
      r.steps≤(3*tapes a+6)*(S+1) :=
  hrow a ds dflt S R B _ hv (fun k hk=>uniform_budget a B R S ds[k] (hv k hk)) k hk out

end NearCubicWires.P1TopDownPaidReusable

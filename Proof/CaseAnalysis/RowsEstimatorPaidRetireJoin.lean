import Proof.CaseAnalysis.RowsEstimatorPaidRetire
import Proof.CaseAnalysis.RowsEstimatorPaidScanned

/-! Append the actual two-word retirement to the completed estimator run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def RetiredJoined {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (worker : Machine (tapes a p) s)
    (fuel bound : ℕ) (initial : Configuration (tapes a p) s) (D : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) : Prop := ∃ A extra r,
  runFrom worker fuel initial=some r ∧ r.final.heads=heads a p word ∧
    r.final.tapes=install (retireSlots a p) (Fin.addCases A extra) (fun _=>List.replicate D false) ∧
    r.steps ≤ bound ∧ Returned p D word fields A ∧
    extra (ScannedClean.fresh a 1)=List.replicate D true

theorem restart_state {n s t : ℕ} (c : Configuration n s) (q : Fin t)
    (H : Fin n → ℕ) (A : Fin n → List Bool) (hh : c.heads=H) (ht : c.tapes=A) :
    Composition.restart c q=(⟨q,H,A⟩ : Configuration n t) := by
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht

theorem retire_join {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (D fuel bound : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) (worker : Machine (tapes a p) s)
    (initial : Configuration (tapes a p) s)
    (hr : WarmJoined a p worker fuel bound initial D word fields) :
    RetiredJoined a p (Composition.machine worker (retire a p)) (fuel+1+(2*D+4))
      (bound+1+(2*D+4)) (Composition.leftConfig 5 initial) D word fields := by
  obtain ⟨A,extra,x,hx,xh,xt,xs,props,xd⟩:=hr
  obtain ⟨y,hy,yh,yt,ys⟩:=retire_run a p D word A extra props.2.2.1 xd
  have hc : Composition.restart x.final (retire a p).start=
      (⟨DriverRetire.machine.start,heads a p word,Fin.addCases A extra⟩ : Configuration (tapes a p) 5) :=
    restart_state x.final _ _ _ xh xt
  rw [←hc] at hy
  have hj:=Composition.run_join worker (retire a p) _ _ _ x y hx hy
  refine ⟨A,extra,Composition.joinedReceipt x y,hj,yh,yt,?_,props,xd⟩
  change x.steps+1+y.steps ≤ bound+1+(2*D+4)
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

import Proof.CaseAnalysis.RowsEstimatorSubstitutionCache

/-! Exact ambient projections keep each actual substitution stage small. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionDock
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem run {t u s n : ℕ} (worker : Machine t s) (slot : Fin t → Fin u)
    (hi : Function.Injective slot) (hin hout : Fin t → ℕ) (tin tout : Fin t → List Bool)
    (H H' : Fin u → ℕ) (A A' : Fin u → List Bool) (raw : Step worker n hin tin hout tout)
    (hhi : ∀ j,H (slot j)=hin j) (hti : ∀ j,A (slot j)=tin j)
    (hho : ∀ j,H' (slot j)=hout j) (hto : ∀ j,A' (slot j)=tout j)
    (hhkeep : ∀ i,(∀ j,slot j≠i) → H i=H' i)
    (htkeep : ∀ i,(∀ j,slot j≠i) → A i=A' i) :
    Step (RecoveryFocus.machine slot worker) n H A H' A' := by
  obtain ⟨base,hb,bh,bt,bs⟩:=raw
  obtain ⟨r,hr,_rc,rs,rh,rt,keep⟩:=RecoveryFocus.dock slot hi worker n H A _ hhi hti base hb
  refine ⟨r,hr,?_,?_,rs.le.trans bs⟩
  · funext i
    by_cases hit : ∃ j,slot j=i
    · obtain ⟨j,rfl⟩:=hit
      exact (rh j).trans ((congrFun bh j).trans (hho j).symm)
    · have hn : ∀ j,slot j≠i:=by simpa using hit
      exact (keep i hn).1.trans (hhkeep i hn)
  · funext i
    by_cases hit : ∃ j,slot j=i
    · obtain ⟨j,rfl⟩:=hit
      exact (rt j).trans ((congrFun bt j).trans (hto j).symm)
    · have hn : ∀ j,slot j≠i:=by simpa using hit
      exact (keep i hn).2.trans (htkeep i hn)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionDock

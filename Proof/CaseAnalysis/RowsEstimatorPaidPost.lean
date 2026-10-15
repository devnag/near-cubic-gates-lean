import Proof.CaseAnalysis.RowsEstimatorPaidOwned
import Proof.CaseAnalysis.RowsEstimatorPaidRetiredBank

/-! Complete public and private projections of the actual retired estimator bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Clean (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) (A : Fin (tapes a p) → List Bool) : Prop where
  output : A (old a p (WarmPrepare.spare p))=word
  work : ∀ i,A (old a p (WarmPrepare.work p i))=List.replicate D false
  driver : A (old a p (WarmPrepare.driver p))=List.replicate D false
  log : A (old a p (WarmPrepare.log p))=List.replicate (D+1) false
  sources : ∀ i,A (old a p (WarmPrepare.source p i))=fields i
  protectedWords : ∀ i : Fin 70,i.val=52 ∨ i.val=68 →
    A (old a p (WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p))))=Scanned.output row C i
  privateWords : ∀ i : Fin (ScannedClean.tapes a),∃ n,A (i.natAdd (WarmPrepare.tapes p))=List.replicate n false

theorem ne_driver (p : Program) (i : Fin (WarmPrepare.tapes p))
    (hi : i.val≠WholePrefix.tapes p+2) : i≠WarmPrepare.driver p := by
  intro he
  have hv:=congrArg (fun j : Fin (WarmPrepare.tapes p)=>j.val) he
  rw [WarmPrepare.driver_val] at hv
  exact hi hv

theorem retired_clean (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool)
    (h : Returned p D word fields A) (hp : Private a extra) (hprotected : Protected p row C A) :
    Clean a p row C D word fields (retiredBank a p D A extra) := by
  refine ⟨?_,?_,retired_driver a p D A extra,?_,?_,?_,retired_private a p D A extra hp⟩
  · rw [retired_public a p D A extra _ (ne_driver p _ (by rw [WarmPrepared.spare_val];omega))]
    exact h.1
  · intro i
    have hne : WarmPrepare.work p i≠WarmPrepare.driver p:=ne_driver p _ (by
      change (Reuse.work p i).val≠WholePrefix.tapes p+2
      have hb:=(Reuse.work_bounds p i).1
      omega)
    rw [retired_public a p D A extra _ hne]
    exact h.2.1 i
  · rw [retired_public a p D A extra _ (ne_driver p _ (by rw [WarmPrepare.log_val];omega))]
    exact h.2.2.2.1
  · intro i
    rw [retired_public a p D A extra _ (ne_driver p _ (by rw [WarmPrepare.source_val];unfold Reuse.tapes;omega))]
    exact h.2.2.2.2 i
  · intro i hi
    have hne : WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p))≠WarmPrepare.driver p:=ne_driver p _ (by
      rw [WarmPrepare.old_val]
      have hn : 70 ≤ WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
      have hb:=i.isLt
      simp only [Fin.val_castAdd]
      omega)
    rw [retired_public a p D A extra _ hne]
    exact hprotected i hi

theorem Owned.clean {s : ℕ} {a : WilliamsAlgorithm} {p : Program} {worker : Machine (tapes a p) s}
    {fuel bound : ℕ} {initial : Configuration (tapes a p) s} {row : EquationRow.Input} {C D : ℕ}
    {word : List Bool} {fields : Fin 7 → List Bool}
    (h : Owned a p worker fuel bound initial row C D word fields) : ∃ r,
    runFrom worker fuel initial=some r ∧ r.final.heads=heads a p word ∧ r.steps ≤ bound ∧
      Clean a p row C D word fields r.final.tapes := by
  obtain ⟨A,extra,r,hr,rh,rt,rs,props,priv,protectedWords⟩:=h
  refine ⟨r,hr,rh,rs,?_⟩
  rw [rt]
  exact retired_clean a p row C D word fields A extra props priv protectedWords

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid

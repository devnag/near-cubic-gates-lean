import Proof.CaseAnalysis.RowsEstimatorPreparedJoin

/-! Symbolic consumer projections avoid unfolding the Williams controller. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem embedded_heads (p : Program) (out : List Bool) :
    Fin.addCases (fun i : Fin (Reuse.tapes p)=>if i=Reuse.output p then out.length else 0)
      (fun _ : Fin 7=>0)=WarmPrepare.heads p out := by
  funext i
  refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,WarmPrepare.heads,WarmPrepare.spare]
    by_cases hj : j=Reuse.output p
    · subst j
      simp only [ite_true]
    · simp only [hj,ite_false]
      split_ifs with hit
      · exact False.elim (hj (Fin.ext (congrArg (fun z : Fin (WarmPrepare.tapes p)=>z.val) hit)))
      · rfl
  · simp only [Fin.addCases_right]
    change 0=WarmPrepare.heads p out (WarmPrepare.source p j)
    simp only [WarmPrepare.heads,source_ne p j,ite_false]

theorem complete {s t : ℕ} (p : Program) (first : Machine (WarmPrepare.tapes p) s)
    (worker : Machine (WholePrefix.tapes p) t) (fq b : ℕ)
    (A B : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ) (fields : Fin 7 → List Bool) (out word : List Bool)
    (x : ExecutionReceipt (WarmPrepare.tapes p) s) (y : ExecutionReceipt (Reuse.tapes p) (t+2+24))
    (hx : runFrom first (4*D+9) ⟨first.start,WarmPrepare.heads p out,
      WarmPrepare.live p (WarmPrepare.data p B D 0 fields) out⟩=some x)
    (xh : x.final.heads=WarmPrepare.heads p out)
    (xt : x.final.tapes=WarmPrepare.live p (WarmPrepare.data p (WarmReuse.padded p D A) D (D+1) fields) out)
    (xs : x.steps=4*D+9)
    (hy : runFrom (WarmReuse.machine p worker) fq (WarmReuse.entry p worker D A out)=some y)
    (ys : y.steps ≤ 4*D+40*b+64)
    (yh : y.final.heads=(fun i=>if i=Reuse.output p then (out++word).length else 0))
    (yt : y.final.tapes (Reuse.output p)=out++word)
    (yw : ∀ i,y.final.tapes (Reuse.work p i)=List.replicate D false)
    (yd : y.final.tapes (Reuse.driver p)=List.replicate D true)
    (yl : y.final.tapes (Reuse.log p)=List.replicate (D+1) false) : ∃ r,
    runFrom (Composition.machine first (TapeEmbedding.machine 7 (WarmReuse.machine p worker))) (4*D+9+1+fq)
      (Composition.leftConfig (t+2+24) ⟨first.start,WarmPrepare.heads p out,
        WarmPrepare.live p (WarmPrepare.data p B D 0 fields) out⟩)=some r ∧
      r.steps ≤ 8*D+40*b+74 ∧
      r.final.heads=WarmPrepare.heads p (out++word) ∧
      r.final.tapes (WarmPrepare.spare p)=out++word ∧
      (∀ i,r.final.tapes (WarmPrepare.work p i)=List.replicate D false) ∧
      r.final.tapes (WarmPrepare.driver p)=List.replicate D true ∧
      r.final.tapes (WarmPrepare.log p)=List.replicate (D+1) false ∧
      (∀ i,r.final.tapes (WarmPrepare.source p i)=fields i) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=join p first worker _ _ A B D fields out x y hx xh xt hy
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rs]
    omega
  · rw [rh,yh]
    exact embedded_heads p _
  · rw [rt]
    exact (Fin.addCases_left (Reuse.output p)).trans yt
  · intro i
    rw [rt]
    exact (Fin.addCases_left (Reuse.work p i)).trans (yw i)
  · rw [rt]
    exact (Fin.addCases_left (Reuse.driver p)).trans yd
  · rw [rt]
    exact (Fin.addCases_left (Reuse.log p)).trans yl
  · intro i
    rw [rt]
    exact Fin.addCases_right i

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared

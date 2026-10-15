import Proof.CaseAnalysis.RowsEstimatorPreparedComplete

/-! Symbolic consumer projections avoid unfolding the Williams controller. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem complete_any {s t : ℕ} (p : Program) (first : Machine (WarmPrepare.tapes p) s)
    (worker : Machine (Reuse.tapes p) t) (source : Configuration (Reuse.tapes p) t) (fq b : ℕ)
    (A B : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ) (fields : Fin 7 → List Bool) (out word : List Bool)
    (x : ExecutionReceipt (WarmPrepare.tapes p) s) (y : ExecutionReceipt (Reuse.tapes p) t)
    (hx : runFrom first (4*D+9) ⟨first.start,WarmPrepare.heads p out,
      WarmPrepare.live p (WarmPrepare.data p B D 0 fields) out⟩=some x)
    (xh : x.final.heads=WarmPrepare.heads p out)
    (xt : x.final.tapes=WarmPrepare.live p (WarmPrepare.data p (WarmReuse.padded p D A) D (D+1) fields) out)
    (xs : x.steps=4*D+9)
    (sourceEq : TapeEmbedding.config (fun _ : Fin 7=>0) fields source=
      (⟨worker.start,WarmPrepare.heads p out,
        WarmPrepare.live p (WarmPrepare.data p (WarmReuse.padded p D A) D (D+1) fields) out⟩ : Configuration (WarmPrepare.tapes p) t))
    (hy : runFrom worker fq source=some y)
    (ys : y.steps ≤ 4*D+40*b+64)
    (yh : y.final.heads=(fun i=>if i=Reuse.output p then (out++word).length else 0))
    (yt : y.final.tapes (Reuse.output p)=out++word)
    (yw : ∀ i,y.final.tapes (Reuse.work p i)=List.replicate D false)
    (yd : y.final.tapes (Reuse.driver p)=List.replicate D true)
    (yl : y.final.tapes (Reuse.log p)=List.replicate (D+1) false) : ∃ r,
    runFrom (Composition.machine first (TapeEmbedding.machine 7 worker)) (4*D+9+1+fq)
      (Composition.leftConfig t ⟨first.start,WarmPrepare.heads p out,
        WarmPrepare.live p (WarmPrepare.data p B D 0 fields) out⟩)=some r ∧
      r.steps ≤ 8*D+40*b+74 ∧
      r.final.heads=WarmPrepare.heads p (out++word) ∧
      r.final.tapes (WarmPrepare.spare p)=out++word ∧
      (∀ i,r.final.tapes (WarmPrepare.work p i)=List.replicate D false) ∧
      r.final.tapes (WarmPrepare.driver p)=List.replicate D true ∧
      r.final.tapes (WarmPrepare.log p)=List.replicate (D+1) false ∧
      (∀ i,r.final.tapes (WarmPrepare.source p i)=fields i) := by
  let z:=TapeEmbedding.receipt (fun _ : Fin 7=>0) fields y
  have hz:=TapeEmbedding.run_embed worker (fun _ : Fin 7=>0) fields _ _ y hy
  have he : Composition.restart x.final (TapeEmbedding.machine 7 worker).start=
      TapeEmbedding.config (fun _ : Fin 7=>0) fields source := by
    rw [sourceEq]
    apply configuration_ext
    · rfl
    · exact xh
    · exact xt
  rw [←he] at hz
  have hr:=Composition.run_join first (TapeEmbedding.machine 7 worker) _ _ _ x z hx hz
  let r:=Composition.joinedReceipt x z
  have rh : r.final.heads=Fin.addCases y.final.heads (fun _ : Fin 7=>0):=rfl
  have rt : r.final.tapes=Fin.addCases y.final.tapes fields:=rfl
  have rs : r.steps=x.steps+1+y.steps:=rfl
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

import Proof.CaseAnalysis.RowsEstimatorPreparedPorts

/-! Symbolic finite-control handoff into the unchanged reusable Warm machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem join {s t : ℕ} (p : Program) (first : Machine (WarmPrepare.tapes p) s)
    (worker : Machine (WholePrefix.tapes p) t) (fp fq : ℕ)
    (A B : Fin (WholePrefix.tapes p) → List Bool) (D : ℕ) (fields : Fin 7 → List Bool) (out : List Bool)
    (x : ExecutionReceipt (WarmPrepare.tapes p) s) (y : ExecutionReceipt (Reuse.tapes p) (t+2+24))
    (hx : runFrom first fp ⟨first.start,WarmPrepare.heads p out,
      WarmPrepare.live p (WarmPrepare.data p B D 0 fields) out⟩=some x)
    (xh : x.final.heads=WarmPrepare.heads p out)
    (xt : x.final.tapes=WarmPrepare.live p (WarmPrepare.data p (WarmReuse.padded p D A) D (D+1) fields) out)
    (hy : runFrom (WarmReuse.machine p worker) fq (WarmReuse.entry p worker D A out)=some y) : ∃ r,
    runFrom (Composition.machine first (TapeEmbedding.machine 7 (WarmReuse.machine p worker))) (fp+1+fq)
      (Composition.leftConfig (t+2+24) ⟨first.start,WarmPrepare.heads p out,
        WarmPrepare.live p (WarmPrepare.data p B D 0 fields) out⟩)=some r ∧
      r.final.heads=Fin.addCases y.final.heads (fun _ : Fin 7=>0) ∧
      r.final.tapes=Fin.addCases y.final.tapes fields ∧ r.steps=x.steps+1+y.steps := by
  let z:=TapeEmbedding.receipt (fun _ : Fin 7=>0) fields y
  have hz:=TapeEmbedding.run_embed (WarmReuse.machine p worker) (fun _ : Fin 7=>0) fields _ _ y hy
  have he : Composition.restart x.final (TapeEmbedding.machine 7 (WarmReuse.machine p worker)).start=
      TapeEmbedding.config (fun _ : Fin 7=>0) fields (WarmReuse.entry p worker D A out) := by
    rw [warm_entry]
    apply configuration_ext
    · rfl
    · exact xh
    · exact xt
  rw [←he] at hz
  have hr:=Composition.run_join first (TapeEmbedding.machine 7 (WarmReuse.machine p worker)) _ _ _ x z hx hz
  exact ⟨Composition.joinedReceipt x z,hr,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared

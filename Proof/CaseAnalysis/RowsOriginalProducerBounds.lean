import Proof.CaseAnalysis.RowsOriginalProducer

/-! The actual fixed-template program discharges every local product Fits
premise from the original single-cache count and encoded-width bounds. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalProducer
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsEstimator CloseoutRowsOriginalTemplates
open CloseoutRowsOriginalMonomial CloseoutRowsRawAtomSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem index_capacity (cs : List (List (List ℕ))) (B W : ℕ) : 8*cs.length+37≤rowC cs B W := by
  have h:=cache_capacity cs B W
  unfold CloseoutRowsOriginalCache.capacity at h
  omega

theorem metadata_budget (r : Row) (hl : r.factors.length≤4) : CloseoutRowsOriginalMetadata.budget r≤39 := by
  unfold CloseoutRowsOriginalMetadata.budget
  rw [CloseoutRowsOriginalMetadata.rho_length]
  simp only [CloseoutRowsOriginalMetadata.count,RepairSource.VerifierDecoding.CompareMachine.word,
    CloseoutRowsOriginalMetadata.parity,List.length_cons,List.length_nil,List.length_replicate]
  omega

theorem bounded_run (r : Row) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ)
    (B W : ℕ) (hB : 1≤B) (count : ∀ p∈cs,p.length≤B)
    (width : ∀ p∈cs,(ExtIncidence.stream p).length≤W)
    (valid : CloseoutRowsOriginalMonomial.Valid cs (r.factors.map indices))
    (hi : ∀ side,indices side<cs.length) (hl : r.factors.length≤4) :
    Step (machine r) (48*rowC cs B W+16*cs.length+203) (heads 0 0 0)
      (data (rowC cs B W) indices [] (cacheWord cs) [] (CloseoutRowsOriginalMetadata.data (rowC cs B W) [] [] []))
      (heads ((r.factors.map indices).flatMap ExtIncidence.block).length 17 1)
      (data (rowC cs B W) indices (CloseoutRowsOriginalWriter.indicesWord indices r.factors) (cacheWord cs)
        (ExtIncidence.stream (value cs (r.factors.map indices) valid [[]]))
        (CloseoutRowsOriginalMetadata.data (rowC cs B W) (CloseoutRowsOriginalMetadata.rho r)
          (CloseoutRowsOriginalMetadata.count r) (CloseoutRowsOriginalMetadata.parity r))) := by
  have length : (r.factors.map indices).length≤4:=by simpa using hl
  have fits:=quartic_fits cs B W hB count width (r.factors.map indices) valid length
  have cap:=cache_capacity cs B W
  have worker:=run r (rowC cs B W) (rowR W) cs.length cs indices valid (fun side=>(hi side).le)
    hl (index_capacity cs B W) cap fits
  have hp:=CloseoutRowsOriginalMonomial.budget_bound (rowC cs B W) (rowR W) cs _ valid [[]] cap fits
  have hw:=CloseoutRowsOriginalWriter.budget_bound indices r.factors cs.length (fun side=>(hi side).le) hl
  have hm:=metadata_budget r hl
  apply worker.enlarge
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalProducer

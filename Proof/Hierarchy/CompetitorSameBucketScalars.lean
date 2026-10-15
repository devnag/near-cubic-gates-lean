import Proof.Hierarchy.CompetitorSameBucketCoefficientTemplate

/-! Retained raw p, D and framed M/U/zero are actual cold output fields.
Determinism identifies each projection with the same executed rank receipt. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdScalars
open LocalBitMultitape RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ranked_scalars (r : Request) (ranked : ExecutionReceipt 306 _)
    (hr : run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r) (MatrixBatchRankReverse.input r)=some ranked) :
    ranked.final.tapes 40=List.replicate r.p true ∧ ranked.final.heads 40=0 ∧
    ranked.final.tapes 32=frame (binary r.M r.U) ∧ ranked.final.heads 32=0 ∧
    ranked.final.tapes 130=List.replicate (MatrixScoreReusableRanks.D r) true ∧ ranked.final.heads 130=0 := by
  obtain ⟨state,original,used,_,ot,oh,hu,ut,uh,_,_,_,_,o40,h40,_,_,_,_,_⟩:=MatrixBatchRetainedFields.retained_run r
  obtain ⟨same,endpoints,hs,he,et,eh,_,_,_,_,_,_,_,_,_⟩:=MatrixBatchBucketEndpoints.raw_run r
  have heq : same=used := Option.some.inj (hs.symm.trans hu)
  subst same
  obtain ⟨same,actual,hs,ha,atapes,ah,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=MatrixBatchRankReverse.raw_run r
  have heq : same=endpoints := Option.some.inj (hs.symm.trans he)
  subst same
  have heq : actual=ranked := Option.some.inj (ha.symm.trans hr)
  subst actual
  have u32 : used.final.tapes 32=frame (binary r.M r.U) :=
    (ut 32).trans ((ot 23).trans (MatrixBatchNativeWidth.native_u r state))
  have u130 : used.final.tapes 130=List.replicate (MatrixScoreReusableRanks.D r) true :=
    (ut 130).trans ((ot 44).trans (MatrixBatchRootCapacity.native_d r state))
  have u32h : used.final.heads 32=0 := by
    have h:=uh 32
    simp only [show (32 : Fin 166)≠39 from by decide,show (32 : Fin 166)≠89 from by decide,or_self,ite_false] at h
    exact h.trans (oh 23)
  have u130h : used.final.heads 130=0 := by
    have h:=uh 130
    simp only [show (130 : Fin 166)≠39 from by decide,show (130 : Fin 166)≠89 from by decide,or_self,ite_false] at h
    exact h.trans (oh 44)
  have u40h : used.final.heads 40=0 := by
    have h:=uh 40
    simp only [show (40 : Fin 166)≠39 from by decide,show (40 : Fin 166)≠89 from by decide,or_self,ite_false] at h
    exact h.trans h40
  refine ⟨(atapes 40 (by decide)).trans ((et 40).trans ((ut 40).trans o40)),?_,
    (atapes 32 (by decide)).trans ((et 32).trans u32),?_,
    (atapes 130 (by decide)).trans ((et 130).trans u130),?_⟩
  · have h:=(ah 40).trans ((eh 40).trans u40h); simpa using h
  · have h:=(ah 32).trans ((eh 32).trans u32h); simpa using h
  · have h:=(ah 130).trans ((eh 130).trans u130h); simpa using h

theorem cold_scalars (r : Request) (w : ℕ) (cold : ExecutionReceipt 342 _)
    (hc : run CompetitorSameBucketCold.machine (CompetitorSameBucketCold.budget r) (CompetitorSameBucketCold.input r w)=some cold) :
    cold.final.tapes 42=List.replicate r.p true ∧ cold.final.heads 42=0 ∧
    cold.final.tapes 34=frame (binary r.M r.U) ∧ cold.final.heads 34=0 ∧
    cold.final.tapes 132=List.replicate (MatrixScoreReusableRanks.D r) true ∧ cold.final.heads 132=0 ∧
    cold.final.tapes 301=frame (binary r.M 0) ∧ cold.final.heads 301=0 ∧
    cold.final.tapes 227=List.replicate r.M true ∧ cold.final.heads 227=0 := by
  obtain ⟨ranked,same,hr,hs,ct,ch,_,_,_,_,_,_,_⟩:=CompetitorSameBucketCold.cold_run r w
  have heq : same=cold := Option.some.inj (hs.symm.trans hc)
  subst same
  obtain ⟨p,hp,u,hu,d,hd⟩:=ranked_scalars r ranked hr
  obtain ⟨_,_,_,_,m,hm,z,hz⟩:=CompetitorSameBucketColdFields.dimensions r ranked hr
  exact ⟨(ct 40).trans p,(ch 40).trans hp,(ct 32).trans u,(ch 32).trans hu,
    (ct 130).trans d,(ch 130).trans hd,(ct 299).trans z,(ch 299).trans hz,(ct 225).trans m,(ch 225).trans hm⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdScalars

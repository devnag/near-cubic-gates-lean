import Proof.Hierarchy.CompetitorSameBucketGateRepeatBounds

/-! Expose the actual B/Buckets and native scalar fields in the same cold
rank receipt. These are deterministic projections of executed producers. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdFields
open LocalBitMultitape RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dimensions (r : Request) (ranked : ExecutionReceipt 306 _)
    (hr : run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r) (MatrixBatchRankReverse.input r)=some ranked) :
    ranked.final.tapes 216=UnaryTemplate.tape (r.bucketSize+1) ∧ ranked.final.heads 216=0 ∧
    ranked.final.tapes 222=UnaryTemplate.tape r.Buckets ∧ ranked.final.heads 222=0 ∧
    ranked.final.tapes 225=List.replicate r.M true ∧ ranked.final.heads 225=0 ∧
    ranked.final.tapes 299=frame (binary r.M 0) ∧ ranked.final.heads 299=0 := by
  obtain ⟨width,native,hw,hn,nt,nh,_,_,_,_,_,_,_⟩:=MatrixBatchNativeDimensions.raw_run r
  obtain ⟨same,hs,w225,h225,_,_,w216,h216,w222,h222,_⟩:=MatrixBatchNativeDimensions.source_fields r
  have heq : same=width := Option.some.inj (hs.symm.trans hw)
  subst same
  obtain ⟨same,used,hs,hu,ut,uh,_,_,_,_,_⟩:=MatrixBatchBucketUsage.raw_run r
  have heq : same=native := Option.some.inj (hs.symm.trans hn)
  subst same
  obtain ⟨same,endpoints,hs,he,et,eh,_,_,_,_,_,_,e299,h299,_⟩:=MatrixBatchBucketEndpoints.raw_run r
  have heq : same=used := Option.some.inj (hs.symm.trans hu)
  subst same
  obtain ⟨same,actual,hs,ha,atapes,ah,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=MatrixBatchRankReverse.raw_run r
  have heq : same=endpoints := Option.some.inj (hs.symm.trans he)
  subst same
  have heq : actual=ranked := Option.some.inj (ha.symm.trans hr)
  subst actual
  refine ⟨(atapes 216 (by decide)).trans ((et 216).trans ((ut 216).trans ((nt 216).trans w216))),?_,
    (atapes 222 (by decide)).trans ((et 222).trans ((ut 222).trans ((nt 222).trans w222))),?_,
    (atapes 225 (by decide)).trans ((et 225).trans ((ut 225).trans ((nt 225).trans w225))),?_,
    (atapes 299 (by decide)).trans e299,?_⟩
  · have h:=(ah 216).trans ((eh 216).trans ((uh 216).trans ((nh 216).trans h216)))
    simpa using h
  · have h:=(ah 222).trans ((eh 222).trans ((uh 222).trans ((nh 222).trans h222)))
    simpa using h
  · have h:=(ah 225).trans ((eh 225).trans ((uh 225).trans ((nh 225).trans h225)))
    simpa using h
  · have h:=(ah 299).trans h299
    simpa using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdFields

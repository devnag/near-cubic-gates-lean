import Proof.Hierarchy.CompetitorSameBucketCoefficient

/-! The C and D capacity tapes belong to the same cold coefficient receipt.
This exposes the exact two drivers for the physical scratch allocator. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdFunding
open LocalBitMultitape
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields (r : Request) (w : ℕ) (actual : ExecutionReceipt 398 _)
    (ha : run CompetitorSameBucketColdCoefficient.machine (CompetitorSameBucketColdCoefficient.budget r)
      (CompetitorSameBucketColdCoefficient.input r w)=some actual) :
    actual.final.tapes 358=List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) true ∧ actual.final.heads 358=0 ∧
    actual.final.tapes 132=List.replicate (MatrixScoreReusableRanks.D r) true ∧ actual.final.heads 132=0 := by
  obtain ⟨blocks,same,hb,hs,ct,ch,_,_,_⟩:=CompetitorSameBucketColdCoefficient.coefficient_run r w
  have heq : same=actual := Option.some.inj (hs.symm.trans ha)
  subst same
  obtain ⟨capacity,same,hc,hs,bt,bh,_,_,_,_,_,_,_⟩:=CompetitorSameBucketColdBlocks.blocks_run r w
  have heq : same=blocks := Option.some.inj (hs.symm.trans hb)
  subst same
  obtain ⟨cold,same,ho,hs,atapes,ah,c358,h358,_⟩:=CompetitorSameBucketColdCapacity.capacity_run r w
  have heq : same=capacity := Option.some.inj (hs.symm.trans hc)
  subst same
  obtain ⟨_,_,_,_,d132,h132,_,_,_,_⟩:=CompetitorSameBucketColdScalars.cold_scalars r w cold ho
  exact ⟨(ct 358).trans ((bt 358).trans c358),(ch 358).trans ((bh 358).trans h358),
    (ct 132).trans ((bt 132).trans ((atapes 132).trans d132)),
    (ch 132).trans ((bh 132).trans ((ah 132).trans h132))⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdFunding

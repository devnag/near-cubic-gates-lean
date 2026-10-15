import Proof.Hierarchy.CompetitorSameBucketZeroGridSemantics

/-! Exact retained reference words needed by the zero-grid cold caller.
These are projections of the same executed cold coefficient receipt. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdReferences
open LocalBitMultitape RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_fields (r : Request) (w : ℕ) (base : ExecutionReceipt 398 _)
    (hb : run CompetitorSameBucketColdCoefficient.machine (CompetitorSameBucketColdCoefficient.budget r)
      (CompetitorSameBucketColdCoefficient.input r w)=some base) :
    base.final.tapes 301=frame (binary r.M 0) ∧ base.final.heads 301=0 ∧
    base.final.tapes 34=frame (binary r.M r.U) ∧ base.final.heads 34=0 ∧
    base.final.tapes 395=frame (List.replicate (r.p+1) false) ∧ base.final.heads 395=0 := by
  obtain ⟨blocks,same,hblocks,hs,ct,ch,z395,h395,_⟩:=CompetitorSameBucketColdCoefficient.coefficient_run r w
  have he : same=base:=Option.some.inj (hs.symm.trans hb)
  subst same
  obtain ⟨capacity,same,hcapacity,hs,bt,bh,_,_,_,_,_,_,_⟩:=CompetitorSameBucketColdBlocks.blocks_run r w
  have he : same=blocks:=Option.some.inj (hs.symm.trans hblocks)
  subst same
  obtain ⟨cold,same,hcold,hs,ot,oh,_,_,_⟩:=CompetitorSameBucketColdCapacity.capacity_run r w
  have he : same=capacity:=Option.some.inj (hs.symm.trans hcapacity)
  subst same
  obtain ⟨_,_,u,uh,_,_,z,zh,_,_⟩:=CompetitorSameBucketColdScalars.cold_scalars r w cold hcold
  exact ⟨(ct 301).trans ((bt 301).trans ((ot 301).trans z)),
    (ch 301).trans ((bh 301).trans ((oh 301).trans zh)),
    (ct 34).trans ((bt 34).trans ((ot 34).trans u)),
    (ch 34).trans ((bh 34).trans ((oh 34).trans uh)),z395,h395⟩

def slots : Fin 7 → Fin 398 := ![41,42,227,301,34,395,358]
def values (r : Request) : Fin 7 → List Bool :=
  ![UnaryTemplate.tape r.U,List.replicate r.p true,List.replicate r.M true,
    frame (binary r.M 0),frame (binary r.M r.U),frame (List.replicate (r.p+1) false),
    List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) true]

theorem fields (r : Request) (w : ℕ) (base : ExecutionReceipt 398 _)
    (hb : run CompetitorSameBucketColdCoefficient.machine (CompetitorSameBucketColdCoefficient.budget r)
      (CompetitorSameBucketColdCoefficient.input r w)=some base) :
    (∀ j,base.final.tapes (slots j)=values r j) ∧ (∀ j,base.final.heads (slots j)=0) := by
  obtain ⟨bt,bh⟩:=CompetitorSameBucketColdRetained.retained r w base hb
  obtain ⟨t301,h301,t34,h34,t395,h395⟩:=source_fields r w base hb
  constructor
  · intro j; fin_cases j
    · exact bt 16
    · exact bt 14
    · exact bt 15
    · exact t301
    · exact t34
    · exact t395
    · exact bt 9
  · intro j; fin_cases j
    · exact bh 16
    · exact bh 14
    · exact bh 15
    · exact h301
    · exact h34
    · exact h395
    · exact bh 9

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdReferences

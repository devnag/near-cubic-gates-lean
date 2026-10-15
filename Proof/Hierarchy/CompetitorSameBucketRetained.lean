import Proof.Hierarchy.CompetitorSameBucketInitialized

/-! Selected retained fields of the same executed cold receipt. These are
the literal gate, zero-grid and sort caller inputs, all with their actual
head positions; no additional data-generation premise is introduced. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdRetained
open LocalBitMultitape RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17 → Fin 398 := ![0,1,2,91,164,218,224,306,340,358,370,376,380,132,42,227,41]
noncomputable def values (r : Request) (w : ℕ) : Fin 17 → List Bool :=
  ![MatrixScoreBatch.physicalInput r,List.replicate w true,[],UnaryTemplate.tape r.Gates,
    MatrixBatchGateNativeLoop.output r,UnaryTemplate.tape (r.bucketSize+1),UnaryTemplate.tape r.Buckets,
    UnaryTemplate.tape (H r),MatrixCoefficientLoop.output r.p r.cuts,
    List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) true,
    UnaryTemplate.tape (4*H r+1),UnaryTemplate.tape ((4*H r+1)*(r.bucketSize+1)),UnaryTemplate.tape (r.bucketSize+1),
    List.replicate (MatrixScoreReusableRanks.D r) true,List.replicate r.p true,List.replicate r.M true,UnaryTemplate.tape r.U]

theorem retained (r : Request) (w : ℕ) (base : ExecutionReceipt 398 _)
    (hb : run CompetitorSameBucketColdCoefficient.machine (CompetitorSameBucketColdCoefficient.budget r)
      (CompetitorSameBucketColdCoefficient.input r w)=some base) :
    (∀ j,base.final.tapes (slots j)=values r w j) ∧ (∀ j,base.final.heads (slots j)=0) := by
  obtain ⟨blocks,same,hblocks,hs,ct,ch,_,_,_⟩:=CompetitorSameBucketColdCoefficient.coefficient_run r w
  have he : same=base:=Option.some.inj (hs.symm.trans hb)
  subst same
  obtain ⟨capacity,same,hcapacity,hs,bt,bh,l370,h370,bl376,h376,b380,h380,_⟩:=CompetitorSameBucketColdBlocks.blocks_run r w
  have he : same=blocks:=Option.some.inj (hs.symm.trans hblocks)
  subst same
  obtain ⟨cold,same,hcold,hs,ot,oh,_,_,_⟩:=CompetitorSameBucketColdCapacity.capacity_run r w
  have he : same=capacity:=Option.some.inj (hs.symm.trans hcapacity)
  subst same
  have oldT (j : Fin 342) : base.final.tapes (j.castAdd 56)=cold.final.tapes j :=
    (ct (j.castAdd 40)).trans ((bt (j.castAdd 18)).trans (ot j))
  have oldH (j : Fin 342) : base.final.heads (j.castAdd 56)=cold.final.heads j :=
    (ch (j.castAdd 40)).trans ((bh (j.castAdd 18)).trans (oh j))
  obtain ⟨ranked,same,hr,hs,rt,rh,coef,hcoef,t1,h1,t2,h2,_⟩:=CompetitorSameBucketCold.cold_run r w
  have he : same=cold:=Option.some.inj (hs.symm.trans hcold)
  subst same
  obtain ⟨b216,h216,b222,h222,m225,h225,_,_⟩:=CompetitorSameBucketColdFields.dimensions r ranked hr
  obtain ⟨t0,h0⟩:=CompetitorSameBucketCold.source_request r ranked hr
  obtain ⟨_,same,_,hs,_,_,r162,h162,u39,h39,g89,h89,_,_,_,_,hh304,h304,_⟩:=MatrixBatchRankReverse.raw_run r
  have he : same=ranked:=Option.some.inj (hs.symm.trans hr)
  subst same
  obtain ⟨rawp,hp,_,_,_,_,_,_,_,_⟩:=CompetitorSameBucketColdScalars.cold_scalars r w cold hcold
  obtain ⟨c358,h358,d132,h132⟩:=CompetitorSameBucketColdFunding.fields r w base hb
  constructor
  · intro j
    fin_cases j
    · exact (oldT 0).trans ((rt 0).trans t0)
    · exact (oldT 1).trans t1
    · exact (oldT 2).trans t2
    · exact (oldT 91).trans ((rt 89).trans g89)
    · exact (oldT 164).trans ((rt 162).trans r162)
    · exact (oldT 218).trans ((rt 216).trans b216)
    · exact (oldT 224).trans ((rt 222).trans b222)
    · exact (oldT 306).trans ((rt 304).trans hh304)
    · exact (oldT 340).trans coef
    · exact c358
    · exact (ct 370).trans l370
    · exact (ct 376).trans bl376
    · exact (ct 380).trans b380
    · exact d132
    · exact (oldT 42).trans rawp
    · exact (oldT 227).trans ((rt 225).trans m225)
    · exact (oldT 41).trans ((rt 39).trans u39)
  · intro j
    fin_cases j
    · exact (oldH 0).trans ((rh 0).trans h0)
    · exact (oldH 1).trans h1
    · exact (oldH 2).trans h2
    · exact (oldH 91).trans ((rh 89).trans h89)
    · exact (oldH 164).trans ((rh 162).trans h162)
    · exact (oldH 218).trans ((rh 216).trans h216)
    · exact (oldH 224).trans ((rh 222).trans h222)
    · exact (oldH 306).trans ((rh 304).trans h304)
    · exact (oldH 340).trans hcoef
    · exact h358
    · exact (ch 370).trans h370
    · exact (ch 376).trans h376
    · exact (ch 380).trans h380
    · exact h132
    · exact (oldH 42).trans hp
    · exact (oldH 227).trans ((rh 225).trans h225)
    · exact (oldH 41).trans ((rh 39).trans h39)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdRetained

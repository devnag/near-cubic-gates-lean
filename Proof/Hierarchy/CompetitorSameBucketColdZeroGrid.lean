import Proof.Hierarchy.CompetitorSameBucketZeroGridEntry

/-! Whole original Request/W to the streamed contributions and canonical
zero grid. The preparatory fields and complete grid are actual run suppliers. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdZeroGrid
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_run (r : Request) (w : ℕ) : ∃ actual,
    run machine (budget r) (input r w)=some actual ∧
    actual.final.tapes 2=output r ∧ actual.final.heads 2=(output r).length ∧
    (∀ j,actual.final.tapes (retainedSlots j)=retainedValues r w j) ∧
    (∀ j,actual.final.heads (retainedSlots j)=0) ∧ actual.steps≤budget r := by
  obtain ⟨embedded,hfirst,selectedH,selectedT,keptT,keptH,bs⟩:=first_run r w
  have hp : 4*(r.p+1)+3≤CompetitorSameBucketBucketBody.scalarCapacity r := by
    simpa [CompetitorSameBucketColdCopyFields.values] using CompetitorSameBucketColdCopyFields.values_fit r 4
  have hm : 4*r.M+3≤CompetitorSameBucketBucketBody.scalarCapacity r := by
    simpa [CompetitorSameBucketColdCopyFields.values] using CompetitorSameBucketColdCopyFields.values_fit r 0
  obtain ⟨localRun,log,hl,lh,lt,ls⟩:=CompetitorSameBucketZeroGridCold.cold_run r.p r.M r.U
    (CompetitorSameBucketBucketBody.scalarCapacity r) (CompetitorSameBucketGateNative.output r) hp hm (count_fit r)
  obtain ⟨final,hf,_,fs,finalHeads,finalTapes,other⟩:=RecoveryFocus.dock slots slots_injective
    CompetitorSameBucketZeroGridCold.machine _ embedded.final.heads embedded.final.tapes _ selectedH selectedT localRun hl
  change runFrom grid (CompetitorSameBucketZeroGridCold.budget r.p r.M r.U
    (CompetitorSameBucketBucketBody.scalarCapacity r)) (Composition.restart embedded.final grid.start)=some final at hf
  have joined:=Composition.run_join first grid _ _ _ embedded final hfirst hf
  refine ⟨Composition.joinedReceipt embedded final,joined,?_,?_,?_,?_,?_⟩
  · change final.final.tapes (slots 5)=_
    rw [finalTapes,lt]
    rfl
  · change final.final.heads (slots 5)=_
    rw [finalHeads,lh]
    rfl
  · intro j
    exact (other (retainedSlots j) (retained_avoids j)).2.trans (keptT j)
  · intro j
    exact (other (retainedSlots j) (retained_avoids j)).1.trans (keptH j)
  · change embedded.steps+1+final.steps≤budget r
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdZeroGrid

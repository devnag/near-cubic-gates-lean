import Proof.Hierarchy.CompetitorSameBucketAllocationFields

/-! Canonical Request/W through actual dimensions, zero coefficient and
both physical scratch allocations. No capacity or blank-work premise is
left at this enclosing cold boundary. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdWorkspace
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first:=TapeEmbedding.machine 44 CompetitorSameBucketColdCoefficient.machine
noncomputable def machine:=Composition.machine first CompetitorSameBucketColdAllocate.machine
def input (r : Request) (w : ℕ) : Fin 442 → List Bool :=
  CompetitorSameBucketColdAllocate.oldTapes (CompetitorSameBucketColdCoefficient.input r w)
def budget (r : Request) := CompetitorSameBucketColdCoefficient.budget r+1+
  CompetitorSameBucketColdAllocate.budget (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r)

theorem workspace_run (r : Request) (w : ℕ) : ∃ base : ExecutionReceipt 398 _,∃ actual,
    run CompetitorSameBucketColdCoefficient.machine (CompetitorSameBucketColdCoefficient.budget r)
      (CompetitorSameBucketColdCoefficient.input r w)=some base ∧
    run machine (budget r) (input r w)=some actual ∧
    (∀ i : Fin 398,actual.final.tapes (i.castAdd 44)=base.final.tapes i) ∧
    (∀ i : Fin 398,actual.final.heads (i.castAdd 44)=base.final.heads i) ∧
    actual.final.tapes=CompetitorSameBucketColdAllocate.output (CompetitorSameBucketBucketBody.scalarCapacity r)
      (MatrixScoreReusableRanks.D r) base.final.tapes ∧
    (∀ i : Fin 44,actual.final.heads (i.natAdd 398)=0) ∧ actual.steps≤budget r := by
  obtain ⟨_,base,_,hb,_,_,_,_,bs⟩:=CompetitorSameBucketColdCoefficient.coefficient_run r w
  obtain ⟨cT,cH,dT,dH⟩:=CompetitorSameBucketColdFunding.fields r w base hb
  have embedded:=TapeEmbedding.run_embed CompetitorSameBucketColdCoefficient.machine (fun _ : Fin 44 => 0)
    (fun _ : Fin 44 => []) _ _ base hb
  let prepared:=TapeEmbedding.receipt (fun _ : Fin 44 => 0) (fun _ : Fin 44 => []) base
  obtain ⟨allocated,ha,ah,atapes,ast⟩:=CompetitorSameBucketColdAllocate.allocate_run
    (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r)
    base.final.heads base.final.tapes cT cH dT dH
  have hi : Composition.restart prepared.final CompetitorSameBucketColdAllocate.machine.start=
      CompetitorSameBucketColdAllocate.cfg CompetitorSameBucketColdAllocate.machine.start base.final.heads base.final.tapes := rfl
  rw [←hi] at ha
  have joined:=Composition.run_join first CompetitorSameBucketColdAllocate.machine _ _ _ prepared allocated embedded ha
  have hin:=MatrixWilliamsProduct.initial_join (e := 44) CompetitorSameBucketColdCoefficient.machine
    CompetitorSameBucketColdAllocate.machine (CompetitorSameBucketColdCoefficient.input r w)
  rw [hin] at joined
  refine ⟨base,Composition.joinedReceipt prepared allocated,hb,joined,?_,?_,atapes,?_,?_⟩
  · intro i
    change allocated.final.tapes (i.castAdd 44)=_
    rw [atapes]
    exact CompetitorSameBucketColdAllocate.output_old _ _ _ cT dT i
  · intro i
    change allocated.final.heads (i.castAdd 44)=_
    rw [ah]
    simp only [CompetitorSameBucketColdAllocate.oldHeads,Fin.addCases_left]
  · intro i
    change allocated.final.heads (i.natAdd 398)=_
    rw [ah]
    simp only [CompetitorSameBucketColdAllocate.oldHeads,Fin.addCases_right]
  · change prepared.steps+1+allocated.steps≤budget r
    rw [ast]
    change base.steps+1+CompetitorSameBucketColdAllocate.budget (CompetitorSameBucketBucketBody.scalarCapacity r)
      (MatrixScoreReusableRanks.D r)≤budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdWorkspace

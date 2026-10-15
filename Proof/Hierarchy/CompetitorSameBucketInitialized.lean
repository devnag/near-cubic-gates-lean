import Proof.Hierarchy.CompetitorSameBucketCopies

/-! The five scalar copies are consumed by their real cold workspace.
There is no supplied zero template or unexecuted allocation at this parent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdInitialized
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem source_fields (r : Request) (w : ℕ) (base : ExecutionReceipt 398 _)
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

noncomputable def machine:=Composition.machine CompetitorSameBucketColdWorkspace.machine CompetitorSameBucketColdCopies.machine
def input:=CompetitorSameBucketColdWorkspace.input
def budget (r : Request):=CompetitorSameBucketColdWorkspace.budget r+1+CompetitorSameBucketColdCopies.budget r

theorem initialized_run (r : Request) (w : ℕ) : ∃ base : ExecutionReceipt 398 _,∃ workspace : ExecutionReceipt 442 _,∃ actual,
    run CompetitorSameBucketColdCoefficient.machine (CompetitorSameBucketColdCoefficient.budget r)
      (CompetitorSameBucketColdCoefficient.input r w)=some base ∧
    run CompetitorSameBucketColdWorkspace.machine (CompetitorSameBucketColdWorkspace.budget r)
      (CompetitorSameBucketColdWorkspace.input r w)=some workspace ∧
    run machine (budget r) (input r w)=some actual ∧
    actual.final.heads=workspace.final.heads ∧
    actual.final.tapes=CompetitorSameBucketColdCopies.output r workspace.final.tapes ∧
    workspace.final.tapes=CompetitorSameBucketColdAllocate.output (CompetitorSameBucketBucketBody.scalarCapacity r)
      (MatrixScoreReusableRanks.D r) base.final.tapes ∧
    (∀ i : Fin 398,workspace.final.tapes (i.castAdd 44)=base.final.tapes i) ∧
    (∀ i : Fin 398,workspace.final.heads (i.castAdd 44)=base.final.heads i) ∧
    (∀ i : Fin 44,workspace.final.heads (i.natAdd 398)=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,workspace,hb,hw,wt,wh,allocated,fresh,ws⟩:=CompetitorSameBucketColdWorkspace.workspace_run r w
  obtain ⟨t301,h301,t34,h34,t395,h395⟩:=source_fields r w base hb
  have s301:workspace.final.tapes 301=frame (binary r.M 0):=(wt 301).trans t301
  have sh301:workspace.final.heads 301=0:=(wh 301).trans h301
  have s34:workspace.final.tapes 34=frame (binary r.M r.U):=(wt 34).trans t34
  have sh34:workspace.final.heads 34=0:=(wh 34).trans h34
  have s395:workspace.final.tapes 395=frame (List.replicate (r.p+1) false):=(wt 395).trans t395
  have sh395:workspace.final.heads 395=0:=(wh 395).trans h395
  have targets (j : Fin 5) : workspace.final.tapes (CompetitorSameBucketColdCopyFields.targetSlot j)=
      List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false := by
    rw [allocated]
    fin_cases j
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 7
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 33
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 25
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 31
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 32
  have logs (j : Fin 2) : workspace.final.tapes ⟨399+j.val,by omega⟩=
      List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false := by
    rw [allocated]
    fin_cases j
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 1
    · exact CompetitorSameBucketColdAllocate.scalar_cell _ _ _ 2
  obtain ⟨copied,hc,cpH,cpT,cpS⟩:=CompetitorSameBucketColdCopies.copies_run r workspace.final.heads workspace.final.tapes
    (by intro j k; fin_cases j <;> fin_cases k
        all_goals first | exact sh301 | exact sh34 | exact sh395 | exact fresh 7 | exact fresh 33 |
          exact fresh 25 | exact fresh 31 | exact fresh 32 | exact fresh 1 | exact fresh 2)
    (by intro j; fin_cases j; exact s301; exact s301; exact s34; exact s395; exact s395)
    targets (logs 0) (logs 1)
  have he : Composition.restart workspace.final CompetitorSameBucketColdCopies.machine.start=
      CompetitorSameBucketColdCopyFields.cfg CompetitorSameBucketColdCopies.machine.start workspace.final.heads workspace.final.tapes := rfl
  rw [←he] at hc
  have joined:=Composition.run_join CompetitorSameBucketColdWorkspace.machine CompetitorSameBucketColdCopies.machine
    _ _ _ workspace copied hw hc
  refine ⟨base,workspace,Composition.joinedReceipt workspace copied,hb,hw,joined,cpH,cpT,allocated,wt,wh,fresh,?_⟩
  change workspace.steps+1+copied.steps≤budget r
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdInitialized

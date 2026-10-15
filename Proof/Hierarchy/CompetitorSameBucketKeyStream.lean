import Proof.Hierarchy.CompetitorSameBucketZeroGridBounds

/-! Physically terminate and rewind the exact contribution-plus-zero key
stream once. The original Request/W/p/M fields remain available to grouping. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdKeyStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketColdZeroGrid (retainedSlots retainedValues)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputSlot (_ : Fin 1) : Fin 455:=2
theorem output_injective : Function.Injective outputSlot := by intro i j _; exact Subsingleton.elim i j
noncomputable def terminate:=RecoveryFocus.machine outputSlot (MatrixUnaryFinish.append false)
noncomputable def beforeRewind:=Composition.machine CompetitorSameBucketColdZeroGrid.machine terminate
noncomputable def prefixBudget (r : Request):=CompetitorSameBucketColdZeroGrid.budget r+2
noncomputable def word (r : Request):=StablePartition.stream (CompetitorSameBucketKeyRecords.records r)

theorem terminate_run (r : Request) (w : ℕ) : ∃ actual,
    run beforeRewind (prefixBudget r) (CompetitorSameBucketColdZeroGrid.input r w)=some actual ∧
    actual.final.tapes 2=word r ∧
    (∀ j,actual.final.tapes (retainedSlots j)=retainedValues r w j) ∧ actual.steps≤prefixBudget r := by
  obtain ⟨base,hb,bt,bh,rt,rh,bs⟩:=CompetitorSameBucketColdZeroGrid.cold_run r w
  obtain ⟨localRun,hl,lf,ls⟩:=MatrixUnaryFinish.append_run false (CompetitorSameBucketColdZeroGrid.output r)
  obtain ⟨last,hLast,_,lastSteps,_,lastTapes,other⟩:=RecoveryFocus.dock outputSlot output_injective
    (MatrixUnaryFinish.append false) 1 base.final.heads base.final.tapes _
    (by intro j; exact bh) (by intro j; exact bt) localRun hl
  change runFrom terminate 1 (Composition.restart base.final terminate.start)=some last at hLast
  have joined:=Composition.run_join CompetitorSameBucketColdZeroGrid.machine terminate _ _ _ base last hb hLast
  have total : CompetitorSameBucketColdZeroGrid.budget r+1+1=prefixBudget r := by unfold prefixBudget; omega
  rw [total] at joined
  refine ⟨Composition.joinedReceipt base last,joined,?_,?_,?_⟩
  · change last.final.tapes (outputSlot 0)=_
    rw [lastTapes,lf]
    change CompetitorSameBucketColdZeroGrid.output r++[false]=word r
    rw [CompetitorSameBucketKeyRecords.output_word]
    rfl
  · intro j
    exact (other (retainedSlots j) (by intro k; fin_cases j <;> fin_cases k <;> decide)).2.trans (rt j)
  · change base.steps+1+last.steps≤prefixBudget r
    rw [lastSteps,ls]
    unfold prefixBudget
    omega

noncomputable def machine:=Rewind.machine beforeRewind
noncomputable def budget (r : Request):=2*prefixBudget r+2
def input (r : Request) (w : ℕ) : Fin 456 → List Bool :=
  Fin.addCases (m := 455) (n := 1) (motive := fun _=>List Bool) (CompetitorSameBucketColdZeroGrid.input r w) (fun _=>[])

theorem cold_run (r : Request) (w : ℕ) : ∃ actual,
    run machine (budget r) (input r w)=some actual ∧
    actual.final.tapes 2=word r ∧
    (∀ j,actual.final.tapes ((retainedSlots j).castAdd 1)=retainedValues r w j) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,rt,bs⟩:=terminate_run r w
  obtain ⟨actual,ha,atapes,ah,ast,_⟩:=Rewind.reset_run beforeRewind (prefixBudget r)
    (CompetitorSameBucketColdZeroGrid.input r w) base hb
  have bound : 2*base.steps+2≤budget r := by unfold budget; omega
  have more:=runFrom_moreFuel machine _ (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨actual,more,(atapes 2).trans bt,?_,ah,ast.trans_le bound⟩
  intro j
  exact (atapes (retainedSlots j)).trans (rt j)

theorem budget_bound (r : Request) : budget r≤150000000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have source:=CompetitorSameBucketColdZeroGrid.budget_bound r
  have pos : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have h : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold budget prefixBudget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdKeyStream

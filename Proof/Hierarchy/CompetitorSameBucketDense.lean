import Proof.Hierarchy.CompetitorSameBucketDenseSource

/-! Whole canonical Request/W to exact dense same-bucket P/N bank. Both
producer and grouping are executed from their actual cold entries, with
physical zero coverage and every fit derived from the request. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketGroup CompetitorSameBucketEntries
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def budget (r : Request) := CompetitorSameBucketColdSorted.budget r+1+groupBudget r
def retainedSlots : Fin 4 → Fin 511 := ![0,1,42,227]

theorem cold_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 2=dense (width r) r.U (entries r) ∧
    (∀ j,actual.final.tapes (retainedSlots j)=CompetitorSameBucketColdZeroGrid.retainedValues r (width r) j) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ budget r := by
  obtain ⟨sorted,prepared,perm,order,hp,pt,p0,ph,ps⟩:=source_run r
  obtain ⟨group,hg,gt,gr,gh,gs⟩:=sorted_group_run r sorted perm order
  obtain ⟨actual,ha,_,ast,ah,atapes,other⟩:=RecoveryFocus.dock groupSlots group_injective
    CompetitorSameBucketGroupCold.machine _ prepared.final.heads prepared.final.tapes
    (initialConfiguration CompetitorSameBucketGroupCold.machine
      (CompetitorSameBucketGroupCold.input (width r) r.p r.M (StablePartition.stream sorted)))
    (by intro j;exact ph _) pt group hg
  change runFrom last (groupBudget r) (Composition.restart prepared.final last.start)=some actual at ha
  have joined:=Composition.run_join first last _ _ _ prepared actual hp ha
  refine ⟨Composition.joinedReceipt prepared actual,joined,(atapes 4).trans gt,?_,?_,?_⟩
  · intro j
    fin_cases j
    · exact (other 0 group_avoids_zero).2.trans p0
    · exact (atapes 1).trans (gr 1)
    · exact (atapes 2).trans (gr 2)
    · exact (atapes 3).trans (gr 3)
  · intro i
    by_cases hi : ∃ j,groupSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      exact (ah j).trans (gh j)
    · exact (other i (by intro j hj;exact hi ⟨j,hj⟩)).1.trans (ph i)
  · change prepared.steps+1+actual.steps ≤ budget r
    rw [ast]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense

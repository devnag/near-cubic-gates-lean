import Proof.Hierarchy.CompetitorSameBucketDenseLayout

/-! The canonical sorted producer supplies every grouping hypothesis and
its actual blank-work entry. The selected tape contracts are transported
once; both same machines and all their charged executions are retained. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketGroup CompetitorSameBucketEntries
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def groupBudget (r : Request) :=
  CompetitorSameBucketGroupCold.budget (width r) r.p r.M (entries r)

theorem sorted_group_run (r : Request) (sorted : List StablePartition.Record)
    (hp : sorted.Perm (CompetitorSameBucketKeyRecords.records r))
    (ho : sorted.Pairwise (fun a b=>RadixSemantics.value (RadixSemantics.word a) ≤
      RadixSemantics.value (RadixSemantics.word b))) :
    ∃ actual,run CompetitorSameBucketGroupCold.machine (groupBudget r)
      (CompetitorSameBucketGroupCold.input (width r) r.p r.M (StablePartition.stream sorted))=some actual ∧
      actual.final.tapes 4=dense (width r) r.U (entries r) ∧
      (∀ i : Fin 4,actual.final.tapes (i.castAdd 49)=
        CompetitorSameBucketGroupCold.retained (width r) r.p r.M (StablePartition.stream sorted) i) ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ groupBudget r := by
  obtain ⟨es,he,hperm⟩:=sorted_witness r sorted hp
  obtain ⟨hd,hbits,hcoverage,_⟩:=sorted_properties r es hperm
  have order : es.Pairwise (fun a b=>RadixSemantics.value (RadixSemantics.word (a.record r.p r.M)) ≤
      RadixSemantics.value (RadixSemantics.word (b.record r.p r.M))) := by
    rw [he,List.pairwise_map] at ho
    exact ho
  have hm : 2*r.U ≤ 2^r.M := by simpa only [two_mul] using MatrixScoreRawRanks.size_fit r
  obtain ⟨actual,ha,atapes,aret,ah,ast⟩:=CompetitorSameBucketGroupCold.cold_run
    (width r) r.U r.p r.M es (by unfold width CompetitorPlaneWidth.width;omega)
    hd hm order hcoverage hbits (sorted_fit r es hperm)
  have hb : CompetitorSameBucketGroupCold.budget (width r) r.p r.M es=groupBudget r := by
    simp only [CompetitorSameBucketGroupCold.budget,CompetitorSameBucketGroupCold.rawBudget,
      CompetitorSameBucketGroupMachine.streamBudget,groupBudget,hperm.length_eq]
  have hw : stream r.p r.M es=StablePartition.stream sorted := by rw [he];rfl
  rw [hb] at ha ast
  rw [hw] at ha aret
  rw [dense_perm (width r) r.U es (entries r) hperm] at atapes
  exact ⟨actual,ha,atapes,aret,ah,ast⟩

theorem group_work_avoids (j : Fin 53) (hj : 4 ≤ j.val) : ∀ i,sourceSlots i≠groupSlots j := by
  intro i h
  have hv:=congrArg (fun x : Fin 511=>x.val) h
  have hr:=source_range i
  rw [group_value] at hv
  split_ifs at hv <;> omega

theorem group_work_blank (r : Request) (j : Fin 53) (hj : 4 ≤ j.val) : input r (groupSlots j)=[] := by
  have hv : 2 ≤ (groupSlots j).val := by
    rw [group_value]
    split_ifs <;> omega
  simp only [input,publicInput,if_neg (by omega : (groupSlots j).val≠0),
    if_neg (by omega : (groupSlots j).val≠1)]

theorem source_fields (r : Request) (sorted : List StablePartition.Record)
    (tapes : Fin 462 → List Bool) (out : Fin 511 → List Bool)
    (bt : tapes 2=StablePartition.stream sorted)
    (br : ∀ i,tapes (CompetitorSameBucketColdSorted.retainedSlots i)=
      CompetitorSameBucketColdZeroGrid.retainedValues r (width r) i)
    (transport : ∀ i,out (sourceSlots i)=tapes i)
    (other : ∀ i,(∀ j,sourceSlots j≠i) → out i=input r i) :
    (∀ j,out (groupSlots j)=CompetitorSameBucketGroupCold.input (width r) r.p r.M
      (StablePartition.stream sorted) j) ∧ out 0=MatrixScoreBatch.physicalInput r := by
  constructor
  · intro j
    rw [group_input]
    by_cases hj : j.val < 4
    · have jcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by
        have hv : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by omega
        rcases hv with h|h|h|h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
      rcases jcases with rfl|rfl|rfl|rfl
      · exact (transport 2).trans bt
      · exact (transport 1).trans (br 1)
      · exact (transport 42).trans (br 2)
      · exact (transport 227).trans (br 3)
    · have hge : 4 ≤ j.val := by omega
      have h0 : j≠0 := by intro h;subst j;contradiction
      have h1 : j≠1 := by intro h;subst j;contradiction
      have h2 : j≠2 := by intro h;subst j;contradiction
      have h3 : j≠3 := by intro h;subst j;contradiction
      simp only [h0,h1,h2,h3,↓reduceIte]
      exact (other _ (group_work_avoids j hge)).trans (group_work_blank r j hge)
  · exact (transport 0).trans (br 0)

theorem source_run (r : Request) : ∃ sorted actual,
    sorted.Perm (CompetitorSameBucketKeyRecords.records r) ∧
    sorted.Pairwise (fun a b=>RadixSemantics.value (RadixSemantics.word a) ≤ RadixSemantics.value (RadixSemantics.word b)) ∧
    run first (CompetitorSameBucketColdSorted.budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (groupSlots j)=
      CompetitorSameBucketGroupCold.input (width r) r.p r.M (StablePartition.stream sorted) j) ∧
    actual.final.tapes 0=MatrixScoreBatch.physicalInput r ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ CompetitorSameBucketColdSorted.budget r := by
  obtain ⟨sorted,base,perm,order,hb,bt,br,bh,bs⟩:=CompetitorSameBucketColdSorted.cold_run r (width r)
  obtain ⟨actual,ha,_,ast,ah,atapes,other⟩:=RecoveryFocus.dock sourceSlots source_injective
    CompetitorSameBucketColdSorted.machine _ (fun _=>0) (input r)
    (initialConfiguration CompetitorSameBucketColdSorted.machine (CompetitorSameBucketColdSorted.input r (width r)))
    (by intro i;rfl) (source_selected r) base hb
  obtain ⟨selected,p0⟩:=source_fields r sorted base.final.tapes actual.final.tapes bt br atapes
    (by intro i hi;exact (other i hi).2)
  refine ⟨sorted,actual,perm,order,ha,selected,p0,?_,ast.trans_le bs⟩
  intro i
  by_cases hi : ∃ j,sourceSlots j=i
  · obtain ⟨j,rfl⟩:=hi
    exact (ah j).trans (bh j)
  · exact (other i (by intro j hj;exact hi ⟨j,hj⟩)).1

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdDense

import Proof.Hierarchy.CompetitorSameBucketKeyStream

/-! The actual cold key producer supplies the existing sorter's only input.
The sorter extracts width, executes its radix passes, and pays its final
rewind. Original Request/W/p/M fields and all heads are retained at zero. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdSorted
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketKeyRecords (records)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def localMachine:=Rewind.machine SortCarrier.machine
def localInput (word : List Bool) (i : Fin 7):=if i=0 then word else []
noncomputable def localBudget (r : Request):=2*SortCarrier.budget (records r)+2

theorem local_run (r : Request) : ∃ sorted actual,
    sorted.Perm (records r) ∧ sorted.Pairwise (fun a b=>RadixSemantics.value (RadixSemantics.word a)≤RadixSemantics.value (RadixSemantics.word b)) ∧
    run localMachine (localBudget r) (localInput (StablePartition.stream (records r)))=some actual ∧
    actual.final.tapes 0=StablePartition.stream sorted ∧ (∀ i,actual.final.heads i=0) ∧ actual.steps≤localBudget r := by
  obtain ⟨sorted,base,perm,order,hb,bt,bs,_⟩:=SortCarrier.raw_sort (records r) (CompetitorSameBucketKeyRecords.sort_uniform r)
  obtain ⟨actual,ha,atapes,ah,ast,_⟩:=Rewind.reset_run SortCarrier.machine _ _ base hb
  have inputEq : Fin.addCases (m := 6) (n := 1) (motive := fun _=>List Bool)
      (SourceHandoff.sourceTapes (StablePartition.stream (records r))) (fun _=>[])=
      localInput (StablePartition.stream (records r)) := by
    funext i; fin_cases i <;> rfl
  rw [inputEq] at ha
  have bound : 2*base.steps+2≤localBudget r := by unfold localBudget; omega
  have more:=runFrom_moreFuel localMachine _ (localBudget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le bound] at more
  exact ⟨sorted,actual,perm,order,more,(atapes 0).trans bt,ah,ast.trans_le bound⟩

def slots (j : Fin 7) : Fin 462 := if j=0 then 2 else ⟨455+j.val,by omega⟩
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first:=TapeEmbedding.machine 6 CompetitorSameBucketColdKeyStream.machine
noncomputable def sort:=RecoveryFocus.machine slots localMachine
noncomputable def machine:=Composition.machine first sort
noncomputable def budget (r : Request):=CompetitorSameBucketColdKeyStream.budget r+1+localBudget r
def input (r : Request) (w : ℕ) : Fin 462 → List Bool :=
  Fin.addCases (m := 456) (n := 6) (motive := fun _=>List Bool) (CompetitorSameBucketColdKeyStream.input r w) (fun _=>[])
def retainedSlots (j : Fin 4) : Fin 462 := (CompetitorSameBucketColdZeroGrid.retainedSlots j).castAdd 7
private theorem retained_avoids (j : Fin 4) : ∀ k,slots k≠retainedSlots j := by
  intro k; fin_cases j <;> fin_cases k <;> decide

theorem cold_run (r : Request) (w : ℕ) : ∃ sorted actual,
    sorted.Perm (records r) ∧ sorted.Pairwise (fun a b=>RadixSemantics.value (RadixSemantics.word a)≤RadixSemantics.value (RadixSemantics.word b)) ∧
    run machine (budget r) (input r w)=some actual ∧ actual.final.tapes 2=StablePartition.stream sorted ∧
    (∀ j,actual.final.tapes (retainedSlots j)=CompetitorSameBucketColdZeroGrid.retainedValues r w j) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,rt,bh,bs⟩:=CompetitorSameBucketColdKeyStream.cold_run r w
  let embedded:=TapeEmbedding.receipt (fun _ : Fin 6=>0) (fun _=>[]) base
  have embeddedRun:=TapeEmbedding.run_embed CompetitorSameBucketColdKeyStream.machine (fun _ : Fin 6=>0)
    (fun _=>[]) _ _ base hb
  have heads0 : ∀ i,embedded.final.heads i=0 := by
    intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [embedded,TapeEmbedding.receipt_heads_old] using bh j
    · change (Fin.addCases (m := 456) (n := 6) (motive := fun _=>ℕ) base.final.heads (fun _=>0)) (j.natAdd 456)=0
      simp only [Fin.addCases_right]
  obtain ⟨sorted,localRun,perm,order,hl,lt,lh,ls⟩:=local_run r
  have selectedT : ∀ j,embedded.final.tapes (slots j)=localInput (StablePartition.stream (records r)) j := by
    intro j
    fin_cases j
    · exact bt
    all_goals rfl
  obtain ⟨final,hf,_,fs,finalHeads,finalTapes,other⟩:=RecoveryFocus.dock slots slots_injective localMachine _
    embedded.final.heads embedded.final.tapes (initialConfiguration localMachine (localInput (StablePartition.stream (records r))))
    (by intro j; exact heads0 _) selectedT localRun hl
  change runFrom sort (localBudget r) (Composition.restart embedded.final sort.start)=some final at hf
  have joined:=Composition.run_join first sort _ _ _ embedded final embeddedRun hf
  have initial:=MatrixWilliamsProduct.initial_join (e := 6) CompetitorSameBucketColdKeyStream.machine sort
    (CompetitorSameBucketColdKeyStream.input r w)
  rw [initial] at joined
  refine ⟨sorted,Composition.joinedReceipt embedded final,perm,order,joined,?_,?_,?_,?_⟩
  · exact (finalTapes 0).trans lt
  · intro j
    have old : embedded.final.tapes (retainedSlots j)=CompetitorSameBucketColdZeroGrid.retainedValues r w j := by
      change (TapeEmbedding.receipt (fun _ : Fin 6=>0) (fun _=>[]) base).final.tapes
        (((CompetitorSameBucketColdZeroGrid.retainedSlots j).castAdd 1).castAdd 6)=_
      rw [TapeEmbedding.receipt_tapes_old]
      exact rt j
    exact (other (retainedSlots j) (retained_avoids j)).2.trans old
  · intro i
    by_cases h : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=h
      exact (finalHeads j).trans (lh j)
    · exact (other i (by intro j hj; exact h ⟨j,hj⟩)).1.trans (heads0 i)
  · change base.steps+1+final.steps≤budget r
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdSorted

import Proof.PCP.ProjectionNormalizationDedup

/-! One paid reset around the complete clause producer. The resulting stream
and its physically produced sentinel count are ready for balanced encoding. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DedupReady
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 12) : Bool := decide (i=2 ∨ i=11)
noncomputable def reset := MaskedReset.machine DedupCold.machine selected
def advance : Machine 13 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=11 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine reset advance
noncomputable def entry (source : List Bool) (pos count : ℕ) :=
  Composition.leftConfig 2 (Rewind.recording (DedupCold.entry DedupCold.machine.start source pos count) 0)
def budget (rows : List SuffixScan.Clause) := 128*((SuffixScan.stream rows).length+1)^3

theorem advance_run (c : Configuration 13 2) (hc : c.control=0) :
    ∃ r,runFrom advance 1 c=some r ∧ r.final.tapes=c.tapes ∧
      (∀ i,r.final.heads i=if i=11 then c.heads i+1 else c.heads i) ∧ r.steps=1 := by
  let f : Configuration 13 2 := ⟨1,(fun i => if i=11 then c.heads i+1 else c.heads i),c.tapes⟩
  have h : step advance c=some f := by
    simp [step,advance,hc]
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : i=11 <;> simp [applyAction,HeadMove.apply,f,hi]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by simp [advance,hc]) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem ready_run (pre suffix : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom machine (budget rows)
      (entry (pre++SuffixScan.stream rows++suffix) pre.length rows.length)=some r ∧
      r.steps ≤ budget rows ∧ r.final.tapes 2=SuffixScan.stream rows.dedup ∧
      r.final.tapes 11=CompareMachine.word rows.dedup.length ∧
      r.final.heads 2=0 ∧ r.final.heads 11=1 := by
  obtain ⟨base,hb,hbs,hout,hcount,_,_⟩ := DedupCold.cold_run pre suffix rows
  have hhead : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run DedupCold.machine _ _ base hb).1 i
    have hi' : i=2 ∨ i=11 := by simpa [selected] using hi
    rcases hi' with rfl|rfl <;> simpa [DedupCold.entry] using h
  obtain ⟨a,ha,haf,hat,_⟩ := MaskedReset.reset_run DedupCold.machine selected _ _ base hb hhead
  obtain ⟨b,hb,hbt,hbh,hbs'⟩ := advance_run (Composition.restart a.final advance.start) rfl
  have h := Composition.run_join reset advance (2*base.steps+2) 1 _ a b ha hb
  have bound : (2*base.steps+2)+1+1 ≤ budget rows := by
    have hc := Dedup.cubic_budget (pre++SuffixScan.stream rows++suffix) pre.length rows
    dsimp only [DedupCold.budget] at hbs
    dsimp only [budget]
    omega
  have hm := runFrom_moreFuel machine _ (budget rows-((2*base.steps+2)+1+1))
    _ (Composition.joinedReceipt a b) h
  rw [Nat.add_sub_of_le bound] at hm
  refine ⟨Composition.joinedReceipt a b,hm,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    rw [hat,hbs']
    exact bound
  · change b.final.tapes 2=_
    rw [hbt,haf]
    exact hout
  · change b.final.tapes 11=_
    rw [hbt,haf]
    exact hcount
  · change b.final.heads 2=0
    rw [hbh,haf]
    rfl
  · change b.final.heads 11=1
    rw [hbh,haf]
    rfl

end NearCubicWires.RepairSource.ProjectionNormalization.DedupReady

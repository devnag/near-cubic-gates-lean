import Proof.Hierarchy.CompetitorMonomialTargetDenominator

/-! Whole actual coefficient/count-to-term producer. It computes the three
exact integer products, widens all fields to the global width, and appends the literal
negative/positive/denominator record consumed by the cold rational fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorRawFieldEmit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources : List (Fin 79) := [71,68,76]
def fields (t : ℕ) (a : CompetitorValidity.Estimate) : Fin 79 → List Bool := fun i =>
  if i.val=71 then binary (width t) a.negative
  else if i.val=68 then binary (width t) a.positive
  else if i.val=76 then binary t a.denominator else []
noncomputable def emitProgram := listProgram (74 : Fin 79) 70 sources
noncomputable def machine := Composition.machine targetProgram emitProgram
def budget (b t : ℕ) := targetBudget b t+20*t+29

theorem stream_eq (t : ℕ) (a : CompetitorValidity.Estimate) :
    stream (fields t a) sources=CompetitorSumFold.termWord t a := by
  simp [stream,fields,sources,CompetitorSumFold.termWord,CompetitorSumFold.fieldStream,
    CompetitorSumFold.termFields,CompetitorSumFold.termTargets]
theorem cost_eq (t : ℕ) (a : CompetitorValidity.Estimate) : listCost (fields t a) sources=20*t+28 := by
  simp [listCost,fields,sources,width]
  omega

theorem record_run (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t) :
    ∃ r,runFrom machine (budget b t)
        (RecoveryCalls.restarted machine (targetHeads pre) (targetInput b t q count denominator pre))=some r ∧
      r.steps≤budget b t ∧
      r.final.heads=targetHeads (pre++CompetitorSumFold.termWord t (contribution q count denominator)) ∧
      r.final.tapes 74=pre++CompetitorSumFold.termWord t (contribution q count denominator) := by
  obtain ⟨first,prepared,hfirst,hfs,hfh,hft,hpos,hneg,hden,hcounter,hprefix⟩ := target_run b t q count denominator pre hp hn hq hc hd htarget
  let a := contribution q count denominator
  have hs : ∀ j∈sources,targetHeads pre j=0 := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j <;> rfl
  have hfields : ∀ j∈sources,prepared j=frame (fields t a j) := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j
    · exact hneg
    · exact hpos
    · exact hden
  have hcap : ∀ j∈sources,2*(fields t a j).length+1≤2*width t+1 := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j
    · simp [fields]
    · simp [fields]
    · simp [fields,width]
      omega
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := list_run (74 : Fin 79) 70 sources (fields t a) (by decide)
    (by intro j hj; simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj;
        rcases hj with hj | hj | hj <;> subst j <;> decide)
    (by intro j hj; simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj;
        rcases hj with hj | hj | hj <;> subst j <;> decide)
    pre (2*width t+1) (targetHeads pre) prepared hs rfl rfl hfields hprefix hcounter hcap
  have he : Composition.restart first.final emitProgram.start=RecoveryCalls.restarted emitProgram (targetHeads pre) prepared := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom emitProgram (listCost (fields t a) sources)
      (Composition.restart first.final emitProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join targetProgram emitProgram _ _ _ first last hfirst hl'
  have hcost : targetBudget b t+1+listCost (fields t a) sources=budget b t := by rw [cost_eq]; unfold budget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b t
    omega
  · change last.final.heads=_
    rw [hlh,stream_eq]
    funext i
    by_cases hi : i=74
    · subst i
      simp [targetHeads,a]
    · have hv : i.val≠74 := fun h => hi (Fin.ext h)
      simp [Function.update_of_ne hi,targetHeads,hv]
  · change last.final.tapes 74=_
    rw [hlt,Function.update_self,stream_eq]

theorem cold_record_run (b t : ℕ) (q : ℚ) (count denominator : ℕ)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t) :
    ∃ r,run machine (budget b t) (targetInput b t q count denominator [])=some r ∧
      r.steps≤budget b t ∧
      r.final.heads=targetHeads (CompetitorSumFold.termWord t (contribution q count denominator)) ∧
      r.final.tapes 74=CompetitorSumFold.termWord t (contribution q count denominator) := by
  obtain ⟨r,hr,hs,hh,ht⟩ := record_run b t q count denominator [] hp hn hq hc hd htarget
  have hi : RecoveryCalls.restarted machine (targetHeads []) (targetInput b t q count denominator [])=
      initialConfiguration machine (targetInput b t q count denominator []) := by
    apply configuration_ext
    · rfl
    · funext i; simp [RecoveryCalls.restarted,targetHeads,initialConfiguration]
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,hs,by simpa only [List.nil_append] using hh,by simpa only [List.nil_append] using ht⟩

theorem budget_bound (b t : ℕ) (htarget : width b≤t) : budget b t≤2500*(t+1)^2 := by
  have hbt : b≤t := by unfold width at htarget; omega
  unfold budget targetBudget prepareBudget width
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget

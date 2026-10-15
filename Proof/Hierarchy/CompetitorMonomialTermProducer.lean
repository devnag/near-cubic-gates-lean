import Proof.Hierarchy.CompetitorMonomialResize

/-! Whole actual coefficient/count-to-term producer. It computes the three
exact integer products, widens the two numerators, and appends the literal
negative/positive/denominator record consumed by the cold rational fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialProducer
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorRawFieldEmit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources : List (Fin 75) := [71,68,38]
def fields (b : ℕ) (a : CompetitorValidity.Estimate) : Fin 75 → List Bool := fun i =>
  if i.val=71 then binary (width (width b)) a.negative
  else if i.val=68 then binary (width (width b)) a.positive
  else if i.val=38 then binary (width b) a.denominator else []
noncomputable def emitProgram := listProgram (74 : Fin 75) 70 sources
noncomputable def machine := Composition.machine prepareProgram emitProgram
def budget (b : ℕ) := prepareBudget b+20*width b+29

theorem stream_eq (b : ℕ) (a : CompetitorValidity.Estimate) :
    stream (fields b a) sources=CompetitorSumFold.termWord (width b) a := by
  simp [stream,fields,sources,CompetitorSumFold.termWord,CompetitorSumFold.fieldStream,
    CompetitorSumFold.termFields,CompetitorSumFold.termTargets]
theorem cost_eq (b : ℕ) (a : CompetitorValidity.Estimate) : listCost (fields b a) sources=20*width b+28 := by
  simp [listCost,fields,sources,width]
  omega

theorem record_run (b : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) :
    ∃ r,runFrom machine (budget b)
        (RecoveryCalls.restarted machine (heads pre) (input b q count denominator pre))=some r ∧
      r.steps≤budget b ∧
      r.final.heads=heads (pre++CompetitorSumFold.termWord (width b) (contribution q count denominator)) ∧
      r.final.tapes 74=pre++CompetitorSumFold.termWord (width b) (contribution q count denominator) := by
  obtain ⟨first,prepared,hfirst,hfs,hfh,hft,hpos,hneg,hden,hcounter,hprefix⟩ := prepare_run b q count denominator pre hp hn hq hc hd
  let a := contribution q count denominator
  have hs : ∀ j∈sources,heads pre j=0 := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j <;> rfl
  have hfields : ∀ j∈sources,prepared j=frame (fields b a j) := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j
    · exact hneg
    · exact hpos
    · exact hden
  have hcap : ∀ j∈sources,2*(fields b a j).length+1≤2*width (width b)+1 := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j
    · simp [fields]
    · simp [fields]
    · simp [fields,width]
      omega
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := list_run (74 : Fin 75) 70 sources (fields b a) (by decide)
    (by intro j hj; simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj;
        rcases hj with hj | hj | hj <;> subst j <;> decide)
    (by intro j hj; simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj;
        rcases hj with hj | hj | hj <;> subst j <;> decide)
    pre (2*width (width b)+1) (heads pre) prepared hs rfl rfl hfields hprefix hcounter hcap
  have he : Composition.restart first.final emitProgram.start=RecoveryCalls.restarted emitProgram (heads pre) prepared := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom emitProgram (listCost (fields b a) sources)
      (Composition.restart first.final emitProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join prepareProgram emitProgram _ _ _ first last hfirst hl'
  have hcost : prepareBudget b+1+listCost (fields b a) sources=budget b := by rw [cost_eq]; unfold budget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b
    omega
  · change last.final.heads=_
    rw [hlh,stream_eq]
    funext i
    by_cases hi : i=74
    · subst i
      simp [heads,a]
    · have hv : i.val≠74 := fun h => hi (Fin.ext h)
      simp [Function.update_of_ne hi,heads,hv]
  · change last.final.tapes 74=_
    rw [hlt,Function.update_self,stream_eq]

theorem cold_record_run (b : ℕ) (q : ℚ) (count denominator : ℕ)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) :
    ∃ r,run machine (budget b) (input b q count denominator [])=some r ∧
      r.steps≤budget b ∧
      r.final.heads=heads (CompetitorSumFold.termWord (width b) (contribution q count denominator)) ∧
      r.final.tapes 74=CompetitorSumFold.termWord (width b) (contribution q count denominator) := by
  obtain ⟨r,hr,hs,hh,ht⟩ := record_run b q count denominator [] hp hn hq hc hd
  have hi : RecoveryCalls.restarted machine (heads []) (input b q count denominator [])=
      initialConfiguration machine (input b q count denominator []) := by
    apply configuration_ext
    · rfl
    · funext i; simp [RecoveryCalls.restarted,heads,initialConfiguration]
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,hs,by simpa only [List.nil_append] using hh,by simpa only [List.nil_append] using ht⟩

theorem budget_bound (b : ℕ) : budget b≤2500*(b+1)^2 := by
  unfold budget prepareBudget width
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorMonomialProducer

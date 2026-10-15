import Proof.CaseAnalysis.RowsEstimatorCoefficientsProducts
import Proof.Hierarchy.CompetitorReusableMonomial

/-! Exact signed-fraction specialization of the original monomial target,
including its paid denominator resize, term append, and reusable support. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Target
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalDecision CompetitorReusableDecision CompetitorRawFieldEmit
open CompetitorMonomialTarget Products
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def targetInput (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool) : Fin 79 → List Bool :=
  Fin.addCases (m := 75) (n := 4) (motive := fun _ => List Bool) (input b t q count denominator pre)
    ![List.replicate t true,[],[],[]]

theorem target_run (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool)
    (hp : q.positive<2^b) (hn : q.negative<2^b) (hq : q.denominator<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t) :
    ∃ r out,runFrom targetProgram (targetBudget b t)
        (RecoveryCalls.restarted targetProgram (targetHeads pre) (targetInput b t q count denominator pre))=some r ∧
      r.steps≤targetBudget b t ∧ r.final.heads=targetHeads pre ∧ r.final.tapes=out ∧
      out 68=frame (binary (width t) (contribution q count denominator).positive) ∧
      out 71=frame (binary (width t) (contribution q count denominator).negative) ∧
      out 76=frame (binary t (contribution q count denominator).denominator) ∧
      out 70=List.replicate (2*width t+1) false ∧ out 74=pre := by
  obtain ⟨base,prepared,hbase,hbs,hbh,hbt,hpos,hneg,hden,hcounter,hpre⟩ :=
    prepare_run b t q count denominator pre hp hn hq hc hd htarget
  let ambient := targetInput b t q count denominator pre
  obtain ⟨first,hfirst,hff,hfs⟩ := RecoveryFocus.run_config outer outer_injective prepareProgram
    (targetHeads pre) ambient _ _ base hbase
  have hi : RecoveryFocus.config outer (targetHeads pre) ambient
      (RecoveryCalls.restarted prepareProgram (heads pre) (input b t q count denominator pre))=
      RecoveryCalls.restarted prefixProgram (targetHeads pre) ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hh : RecoveryFocus.pick outer i with
      | none => simp [RecoveryFocus.config,hh,RecoveryCalls.restarted]
      | some j =>
        have he := RecoveryFocus.slot_of_pick outer hh
        simp only [RecoveryFocus.config,hh,RecoveryCalls.restarted]
        change targetHeads pre (outer j)=targetHeads pre i
        exact congrArg (targetHeads pre) he
    · exact install_existing outer ambient (input b t q count denominator pre)
        (by intro i; simp [ambient,targetInput,outer])
  rw [hi] at hfirst
  have hfh : first.final.heads=targetHeads pre := by
    rw [hff]
    funext i
    cases hh : RecoveryFocus.pick outer i with
    | none => simp [RecoveryFocus.config,hh]
    | some j =>
      have he := RecoveryFocus.slot_of_pick outer hh
      simp only [RecoveryFocus.config,hh,hbh]
      change targetHeads pre (outer j)=targetHeads pre i
      exact congrArg (targetHeads pre) he
  let wide := install outer ambient prepared
  have hft : first.final.tapes=wide := by rw [hff]; change install outer ambient base.final.tapes=wide; rw [hbt]
  obtain ⟨denRun,hdRun,_,_,hd2,_,_,hdh,hds⟩ := ClockScalarFields.scalar_run t
    (binary (width b) (contribution q count denominator).denominator) (by simpa using htarget)
  have hdenFit : (contribution q count denominator).denominator<2^width b := product_fit b _ _ hq hd
  rw [binary_value (width b) (contribution q count denominator).denominator hdenFit] at hd2
  have denReady : ClockJoin.ReadyRun ClockNormalize.machine (4*t+4)
      (ClockNormalize.input t (binary (width b) (contribution q count denominator).denominator)) denRun.final.tapes :=
    ⟨denRun,hdRun,rfl,hdh,hds.le⟩
  have hdh' : ∀ i,targetHeads pre (denominatorSlots i)=0 := by intro i; fin_cases i <;> rfl
  have hdt : ∀ i,wide (denominatorSlots i)=ClockNormalize.input t
      (binary (width b) (contribution q count denominator).denominator) i := by
    intro i
    fin_cases i
    · exact install_other outer _ _ 75 (fun j => outer_other j 75 (by decide))
    · exact (install_slot outer outer_injective _ prepared 38).trans hden
    · exact install_other outer _ _ 76 (fun j => outer_other j 76 (by decide))
    · exact install_other outer _ _ 77 (fun j => outer_other j 77 (by decide))
    · exact install_other outer _ _ 78 (fun j => outer_other j 78 (by decide))
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := bounded_focused_run denominatorSlots (by decide) _ _ _ denReady
    (targetHeads pre) wide hdh' hdt
  have he : Composition.restart first.final denominatorProgram.start=RecoveryCalls.restarted denominatorProgram (targetHeads pre) wide := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom denominatorProgram (4*t+4) (Composition.restart first.final denominatorProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join prefixProgram denominatorProgram _ _ _ first last hfirst hl'
  have hcost : prepareBudget b t+1+(4*t+4)=targetBudget b t := by unfold targetBudget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,install denominatorSlots wide denRun.final.tapes,hall,?_,hlh,hlt,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤targetBudget b t
    omega
  · exact (install_other denominatorSlots _ _ 68 (by decide)).trans ((install_slot outer outer_injective _ prepared 68).trans hpos)
  · exact (install_other denominatorSlots _ _ 71 (by decide)).trans ((install_slot outer outer_injective _ prepared 71).trans hneg)
  · exact (install_slot denominatorSlots (by decide) _ denRun.final.tapes 2).trans hd2
  · exact (install_other denominatorSlots _ _ 70 (by decide)).trans ((install_slot outer outer_injective _ prepared 70).trans hcounter)
  · exact (install_other denominatorSlots _ _ 74 (by decide)).trans ((install_slot outer outer_injective _ prepared 74).trans hpre)

theorem record_run (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool)
    (hp : q.positive<2^b) (hn : q.negative<2^b) (hq : q.denominator<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t) :
    ∃ r,runFrom CompetitorMonomialTarget.machine (budget b t)
        (RecoveryCalls.restarted CompetitorMonomialTarget.machine (targetHeads pre) (targetInput b t q count denominator pre))=some r ∧
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

def paddedInput (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool) : Fin 79 → List Bool :=
  fun i => ZeroPadding.pad (CompetitorMonomialTarget.padding t i) (targetInput b t q count denominator pre i)

theorem input_support (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool)
    (htarget : width b≤t) (hpre : pre.length≤100*(t+1)^2) (i : Fin 79) :
    (targetInput b t q count denominator pre i).length≤CompetitorReusableDecision.capacity t := by
  have hbt : b≤t := by unfold width at htarget; omega
  have hcap : CompetitorReusableDecision.capacity b≤CompetitorReusableDecision.capacity t := by
    unfold CompetitorReusableDecision.capacity
    nlinarith
  have hw : width t≤CompetitorReusableDecision.capacity t := by
    unfold width CompetitorReusableDecision.capacity
    nlinarith
  have ht : t≤CompetitorReusableDecision.capacity t := by unfold CompetitorReusableDecision.capacity; nlinarith
  have hp : pre.length≤CompetitorReusableDecision.capacity t := by unfold CompetitorReusableDecision.capacity; omega
  have hnative (j : Fin 75) : (input b t q count denominator pre j).length≤CompetitorReusableDecision.capacity t := by
    unfold input
    split
    · next hj =>
      exact (CompetitorReusableDecision.input_support b (operands q) denominator count ⟨j.val,hj⟩).trans hcap
    · split
      · simpa using hw
      · split
        · exact hp
        · simp
  refine Fin.addCases (m := 75) (n := 4) ?_ ?_ i
  · intro j
    simpa [targetInput] using hnative j
  · intro j
    simp only [targetInput,Fin.addCases_right]
    fin_cases j
    · simpa using ht
    · simp
    · simp
    · simp

theorem padded_record_run (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool)
    (hp : q.positive<2^b) (hn : q.negative<2^b) (hq : q.denominator<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t)
    (hpre : pre.length≤100*(t+1)^2) :
    ∃ r out,runFrom CompetitorMonomialTarget.machine (budget b t)
        (RecoveryCalls.restarted CompetitorMonomialTarget.machine (targetHeads pre) (paddedInput b t q count denominator pre))=some r ∧
      r.steps≤budget b t ∧ r.final.tapes=out ∧
      r.final.heads=targetHeads (pre++CompetitorSumFold.termWord t (contribution q count denominator)) ∧
      out 74=pre++CompetitorSumFold.termWord t (contribution q count denominator) ∧
      (∀ i,(out i).length≤CompetitorReusableDecision.capacity t) := by
  obtain ⟨base,hr,hs,hh,ht⟩ := record_run b t q count denominator pre hp hn hq hc hd htarget
  have hsteps := hs.trans (budget_bound b t htarget)
  have hend : pre.length+base.steps+1≤CompetitorReusableDecision.capacity t := by
    unfold CompetitorReusableDecision.capacity
    have hpos : 0<(t+1)^2 := by positivity
    omega
  have hsupport := RecoveryTapeSupport.run_support CompetitorMonomialTarget.machine _ _ base hr (CompetitorReusableDecision.capacity t) pre.length
    (by intro i; simp [RecoveryCalls.restarted,targetHeads]; split <;> omega)
    (by intro i; exact (input_support b t q count denominator pre htarget hpre i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 79) : (base.final.tapes i).length≤CompetitorReusableDecision.capacity t := by
    simpa only [max_eq_left hend] using hsupport i
  obtain ⟨r,hrun,hf,hstep,_⟩ := ZeroPadding.run_config CompetitorMonomialTarget.machine (CompetitorMonomialTarget.padding t) _ _ base hr
  refine ⟨r,r.final.tapes,hrun,hstep.trans_le hs,rfl,?_,?_,?_⟩
  · rw [hf]
    exact hh
  · simpa [hf,ZeroPadding.config,CompetitorMonomialTarget.padding] using ht
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold CompetitorMonomialTarget.padding; split <;> omega) (hbound i)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Target

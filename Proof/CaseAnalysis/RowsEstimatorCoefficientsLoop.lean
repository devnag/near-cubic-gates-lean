import Proof.CaseAnalysis.RowsEstimatorCoefficientsBody
import Proof.Hierarchy.CompetitorMonomialEntry

/-! The original finite scalar-stream loop and cold entry, specialized to
signed Estimate coefficients. All repeated controllers, drivers and budgets
are the accepted ones; only the coefficient representation is generalized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Stream
open CompetitorMonomialStream
def entryWord (b : ℕ) (a : Entry) := recordWord b a.coefficient a.count a.denominator
def words (b : ℕ) (xs : List Entry) := xs.flatMap (entryWord b)
def contributions (xs : List Entry) := xs.map Entry.estimate
def termWords (t : ℕ) (xs : List Entry) := CompetitorSumFold.words t (contributions xs)
theorem termWords_cons (t : ℕ) (a : Entry) (xs : List Entry) :
    termWords t (a::xs)=CompetitorSumFold.termWord t a.estimate++termWords t xs := by
  simp [termWords,contributions,CompetitorSumFold.words]
theorem termWords_length (t : ℕ) (xs : List Entry) : (termWords t xs).length=xs.length*(10*t+11) := by
  induction xs with
  | nil => simp [termWords,contributions,CompetitorSumFold.words]
  | cons a xs ih => rw [termWords_cons,List.length_append,CompetitorSumFold.term_length,ih,List.length_cons]; ring

theorem loop_driver_run (b t : ℕ) (xs : List Entry) (total pos : ℕ) (pre suffix output : List Bool)
    (ambient : Fin 88 → List Bool) (hn : pos+xs.length=total)
    (hv : ∀ a∈xs,a.Valid b) (htarget : width b≤t)
    (hsize : output.length+xs.length*(10*t+11)≤100*(t+1)^2)
    (hstore : Store b t (pre++words b xs++suffix) output ambient) :
    ∃ r out,runFrom loopProgram (xs.length*(bodyBudget t+2)+total+3)
        (RepeatMachine.cfg 0 (cfg output.length bodyProgram.start pre.length ambient) total (pos+1))=some r ∧
      r.steps≤xs.length*(bodyBudget t+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3
        (cfg (output++termWords t xs).length bodyProgram.start (pre.length+(words b xs).length) out) total 1 ∧
      Store b t (pre++words b xs++suffix) (output++termWords t xs) out := by
  induction xs generalizing pos pre output ambient with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust bodyProgram accepted
      (cfg output.length bodyProgram.start pre.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,ambient,by simpa [loopProgram] using hr,by simpa using hs.le,?_,?_⟩
    · simpa [words,termWords,contributions,CompetitorSumFold.words] using hf
    · simpa [words,termWords,contributions,CompetitorSumFold.words] using hstore
  | cons a xs ih =>
    have ha := hv a (by simp)
    obtain ⟨body,hbody,hsteps,hhead,hnext⟩ := body_run b t a.coefficient a.count a.denominator pre
      (words b xs++suffix) output ambient (by simpa [words,entryWord,List.append_assoc] using hstore)
      ha.positive ha.negative ha.coefficientDenominator ha.count ha.denominator htarget (by omega)
    have hp := RepeatMachine.iteration bodyProgram accepted
      (cfg output.length bodyProgram.start pre.length ambient) total pos body rfl
      (by simp only [List.length_cons] at hn; omega) hbody
    simp only [accepted,if_true] at hp
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg (output++CompetitorSumFold.termWord t a.estimate).length bodyProgram.start
          (pre++entryWord b a).length body.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hhead,cfg,List.length_append,entryWord,Entry.estimate]
      · rfl
    rw [hend] at hp
    have hsize' : (output++CompetitorSumFold.termWord t a.estimate).length+xs.length*(10*t+11)≤100*(t+1)^2 := by
      rw [List.length_append,CompetitorSumFold.term_length]
      simp only [List.length_cons] at hsize
      nlinarith
    obtain ⟨tail,out,htail,hts,htf,hto⟩ := ih (pos+1) (pre++entryWord b a)
      (output++CompetitorSumFold.termWord t a.estimate) body.final.tapes
      (by simp only [List.length_cons] at hn; omega) (fun c hc => hv c (by simp [hc])) hsize'
      (by simpa [List.append_assoc,entryWord,Entry.estimate] using hnext)
    have htail' : runFrom loopProgram (xs.length*(bodyBudget t+2)+total+3)
        (RepeatMachine.cfg 0 (cfg (output++CompetitorSumFold.termWord t a.estimate).length bodyProgram.start
          (pre++entryWord b a).length body.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases hp with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(xs.length*(bodyBudget t+2)+total+3)≤
        (a::xs).length*(bodyBudget t+2)+total+3 := by simp only [List.length_cons]; nlinarith
    have hmore := runFrom_moreFuel loopProgram _
      ((a::xs).length*(bodyBudget t+2)+total+3-((body.steps+2)+(xs.length*(bodyBudget t+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,out,hmore,?_,?_,?_⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf,termWords_cons]
      simp [words,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [words,termWords_cons,List.append_assoc] using hto

theorem stream_run (b t : ℕ) (xs : List Entry) (ambient : Fin 88 → List Bool)
    (hv : ∀ a∈xs,a.Valid b) (htarget : width b≤t) (hn : xs.length≤t)
    (hstore : Store b t (words b xs) [] ambient) :
    ∃ r out,runFrom loopProgram (loopBudget t xs.length)
        (RepeatMachine.cfg 0 (cfg 0 bodyProgram.start 0 ambient) xs.length 1)=some r ∧
      r.steps≤loopBudget t xs.length ∧
      r.final=RepeatMachine.cfg 3
        (cfg (termWords t xs).length bodyProgram.start (words b xs).length out) xs.length 1 ∧
      Store b t (words b xs) (termWords t xs) out ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  have hsize : ([] : List Bool).length+xs.length*(10*t+11)≤100*(t+1)^2 := by simp only [List.length_nil]; nlinarith
  obtain ⟨r,out,hr,hs,hf,ho⟩ := loop_driver_run b t xs xs.length 0 [] [] [] ambient (by omega)
    hv htarget hsize (by simpa using hstore)
  have he : xs.length*(bodyBudget t+2)+xs.length+3=loopBudget t xs.length := by unfold loopBudget; ring
  refine ⟨r,out,?_,?_,?_,?_,?_⟩
  · simpa only [he,List.length_nil,Nat.zero_add] using hr
  · simpa only [he] using hs
  · simpa using hf
  · simpa using ho
  · intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact c.valid_estimate b (hv c hc)

end Stream

namespace EntryMachine
open Stream CompetitorMonomialEntry
open CompetitorMonomialStream (coldInput zeroed cold_clear_run zeroed_store Store loopProgram loopBudget cfg bodyProgram heads)

def input (b t : ℕ) (xs : List Entry) := extendTapes (coldInput b t (words b xs)) xs.length
theorem boot_run (b t : ℕ) (xs : List Entry) :
    ClockJoin.ReadyRun bootProgram (2*capacity t+4) (input b t xs)
      (extendTapes (zeroed b t (words b xs)) xs.length) := by
  have hin : ∀ j,input b t xs (outerSlots j)=coldInput b t (words b xs) j := by simp [input,extendTapes,outerSlots]
  have hf := CompetitorRationalProducts.bounded_focus outerSlots outer_injective _ _ _ (cold_clear_run b t (words b xs)) (input b t xs) hin
  have he : install outerSlots (input b t xs) (zeroed b t (words b xs))=
      extendTapes (zeroed b t (words b xs)) xs.length := by
    funext i
    refine Fin.addCases (m := 88) (n := 1) ?_ ?_ i
    · intro j
      simp only [extendTapes,Fin.addCases_left]
      change install outerSlots _ _ (outerSlots j)=_
      exact install_slot outerSlots outer_injective _ _ j
    · intro j
      fin_cases j
      apply install_other
      intro k hk
      have hv := congrArg Fin.val hk
      change k.val=88 at hv
      omega
  rw [he] at hf
  exact hf

theorem cold_stream_run (b t : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (htarget : width b≤t) (hn : xs.length≤t) :
    ∃ r out,run program (budget t xs.length) (input b t xs)=some r ∧ r.steps≤budget t xs.length ∧
      r.final.tapes=extendTapes out xs.length ∧ Store b t (words b xs) (termWords t xs) out ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  obtain ⟨boot,hboot,hbt,hbh,hbs⟩ := boot_run b t xs
  let startTapes := zeroed b t (words b xs)
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run (extendTapes startTapes xs.length)
  obtain ⟨loop,out,hloop,hloops,hloopf,hout,hvalid⟩ := stream_run b t xs startTapes hv htarget hn (zeroed_store b t (words b xs))
  have heLoop : Composition.restart start.final loopProgram.start=
      RepeatMachine.cfg 0 (cfg 0 bodyProgram.start 0 startTapes) xs.length 1 := by
    rw [hstartf]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 88) (n := 1) ?_ ?_ i
      · intro j
        have hj : j.val≠88 := by omega
        simp [Composition.restart,loopHeads,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,heads,hj]
      · intro j
        fin_cases j
        rfl
    · rfl
  have hl' : runFrom loopProgram (loopBudget t xs.length) (Composition.restart start.final loopProgram.start)=some loop := by rw [heLoop]; exact hloop
  have htail := Composition.run_join enter loopProgram _ _ _ start loop hstart hl'
  let tail := Composition.joinedReceipt start loop
  have heStart : Composition.restart boot.final tailProgram.start=
      Composition.leftConfig _ (initialConfiguration enter (extendTapes startTapes xs.length)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hbh i
    · exact hbt
  have ht' : runFrom tailProgram (1+1+loopBudget t xs.length) (Composition.restart boot.final tailProgram.start)=some tail := by rw [heStart]; exact htail
  have hall := Composition.run_join bootProgram tailProgram _ _ _ boot tail hboot ht'
  have hcost : (2*capacity t+4)+1+(1+1+loopBudget t xs.length)=budget t xs.length := by unfold budget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt boot tail,out,hall,?_,?_,hout,hvalid⟩
  · change boot.steps+1+(start.steps+1+loop.steps)≤budget t xs.length
    omega
  · change loop.final.tapes=extendTapes out xs.length
    rw [hloopf]
    rfl

def readyInput (b t : ℕ) (xs : List Entry) : Fin 90 → List Bool :=
  Fin.addCases (m := 89) (n := 1) (motive := fun _ => List Bool) (input b t xs) (fun _ => [])
theorem ready_stream_run (b t : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (htarget : width b≤t) (hn : xs.length≤t) :
    ∃ out,ClockJoin.ReadyRun CompetitorMonomialEntry.machine (readyBudget t xs.length) (readyInput b t xs) out ∧
      out 74=termWords t xs ∧ out 83=List.replicate t true ∧ out 88=CompareMachine.word xs.length ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  obtain ⟨base,store,hr,hs,ht,hstore,hvalid⟩ := cold_stream_run b t xs hv htarget hn
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run program _ _ base hr
  have hc : 2*base.steps+2≤readyBudget t xs.length := by unfold readyBudget; omega
  have hmore := runFrom_moreFuel CompetitorMonomialEntry.machine _ (readyBudget t xs.length-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,?_,?_,?_,hvalid⟩
  · exact (hrt 74).trans (congrFun ht 74) |>.trans hstore.output
  · exact (hrt 83).trans (congrFun ht 83) |>.trans hstore.shortWidth
  · exact (hrt 88).trans (congrFun ht 88)

end EntryMachine
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients

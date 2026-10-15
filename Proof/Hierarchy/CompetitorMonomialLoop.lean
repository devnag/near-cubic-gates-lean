import Proof.Hierarchy.CompetitorMonomialBody

/-! The actual repeated coefficient/count stream producer. Its sole global
append tape is never rewound inside the loop, and the physical unary driver
is returned after exactly the requested number of records. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 88 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine bodyProgram accepted
def entryWord (b : ℕ) (a : Entry) := recordWord b a.coefficient a.count a.denominator
def words (b : ℕ) (xs : List Entry) := xs.flatMap (entryWord b)
def contributions (xs : List Entry) := xs.map Entry.estimate
def termWords (t : ℕ) (xs : List Entry) := CompetitorSumFold.words t (contributions xs)
def loopBudget (t n : ℕ) := n*(bodyBudget t+3)+3

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

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream

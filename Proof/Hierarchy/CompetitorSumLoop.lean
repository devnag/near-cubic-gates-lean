import Proof.Hierarchy.CompetitorSumBody

/-! Whole physical repetition of the exact signed-rational fold. The unary
term driver is exhausted and rewound; each iteration updates the same
accumulator and consumes exactly one three-field scalar record. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 94 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine bodyProgram accepted
def words (b : ℕ) (xs : List CompetitorValidity.Estimate) := xs.flatMap (termWord b)
def folded : CompetitorValidity.Estimate → List CompetitorValidity.Estimate → CompetitorValidity.Estimate
  | a,[] => a
  | a,c::cs => folded (CompetitorRationalNumerators.add a c) cs
def loopBudget (b n : ℕ) := n*(bodyBudget b+3)+3

theorem folded_value (b : ℕ) (a : CompetitorValidity.Estimate) (xs : List CompetitorValidity.Estimate)
    (hv : CompetitorSumWidth.Trace b a xs) :
    (folded a xs).value=a.value+(xs.map CompetitorValidity.Estimate.value).sum := by
  induction xs generalizing a with
  | nil => simp [folded]
  | cons c cs ih =>
    rw [folded,ih _ hv.2.2,CompetitorRationalNumerators.add_value a c hv.1.denominatorPositive hv.2.1.denominatorPositive]
    simp only [List.map_cons,List.sum_cons]
    ring

theorem loop_driver_run (b : ℕ) (a : CompetitorValidity.Estimate) (xs : List CompetitorValidity.Estimate)
    (total pos : ℕ) (pre suffix : List Bool) (ambient : Fin 94 → List Bool) (hn : pos+xs.length=total)
    (hv : CompetitorSumWidth.Trace b a xs) (hstore : Store b a (pre++words b xs++suffix) ambient) :
    ∃ r out,runFrom loopProgram (xs.length*(bodyBudget b+2)+total+3)
        (RepeatMachine.cfg 0 (cfg bodyProgram.start pre.length ambient) total (pos+1))=some r ∧
      r.steps≤xs.length*(bodyBudget b+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3 (cfg bodyProgram.start (pre.length+(words b xs).length) out) total 1 ∧
      Store b (folded a xs) (pre++words b xs++suffix) out := by
  induction xs generalizing a pos pre ambient with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust bodyProgram accepted
      (cfg bodyProgram.start pre.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,ambient,by simpa [loopProgram] using hr,by simpa using hs.le,?_,hstore⟩
    simpa [words] using hf
  | cons c cs ih =>
    obtain ⟨body,hbody,hhead,hnext,hsteps⟩ := body_run b a c pre (words b cs++suffix) ambient
      (by simpa [words,List.append_assoc] using hstore) hv.1 hv.2.1
    have hp := RepeatMachine.iteration bodyProgram accepted
      (cfg bodyProgram.start pre.length ambient) total pos body rfl (by simp only [List.length_cons] at hn; omega) hbody
    simp only [accepted,if_true] at hp
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg bodyProgram.start (pre++termWord b c).length body.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hhead,cfg,List.length_append]
      · rfl
    rw [hend] at hp
    obtain ⟨tail,out,htail,hts,htf,hto⟩ := ih (CompetitorRationalNumerators.add a c) (pos+1)
      (pre++termWord b c) body.final.tapes (by simp only [List.length_cons] at hn; omega) hv.2.2
      (by simpa [List.append_assoc] using hnext)
    have htail' : runFrom loopProgram (cs.length*(bodyBudget b+2)+total+3)
        (RepeatMachine.cfg 0 (cfg bodyProgram.start (pre++termWord b c).length body.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases hp with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(cs.length*(bodyBudget b+2)+total+3)≤
        (c::cs).length*(bodyBudget b+2)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have hmore := runFrom_moreFuel loopProgram _
      ((c::cs).length*(bodyBudget b+2)+total+3-((body.steps+2)+(cs.length*(bodyBudget b+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,out,hmore,?_,?_,?_⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf]
      simp [words,List.length_append,Nat.add_assoc]
    · simpa [folded,words,List.append_assoc] using hto

theorem sum_loop_run (b : ℕ) (a : CompetitorValidity.Estimate) (xs : List CompetitorValidity.Estimate)
    (ambient : Fin 94 → List Bool) (hv : CompetitorSumWidth.Trace b a xs)
    (hstore : Store b a (words b xs) ambient) :
    ∃ r out,runFrom loopProgram (loopBudget b xs.length)
        (RepeatMachine.cfg 0 (cfg bodyProgram.start 0 ambient) xs.length 1)=some r ∧
      r.steps≤loopBudget b xs.length ∧
      r.final=RepeatMachine.cfg 3 (cfg bodyProgram.start (words b xs).length out) xs.length 1 ∧
      Store b (folded a xs) (words b xs) out ∧
      (folded a xs).value=a.value+(xs.map CompetitorValidity.Estimate.value).sum := by
  obtain ⟨r,out,hr,hs,hf,ho⟩ := loop_driver_run b a xs xs.length 0 [] [] ambient (by omega) hv (by simpa using hstore)
  have he : xs.length*(bodyBudget b+2)+xs.length+3=loopBudget b xs.length := by
    unfold loopBudget
    ring
  refine ⟨r,out,?_,?_,?_,?_,folded_value b a xs hv⟩
  · simpa only [he,List.length_nil,Nat.zero_add] using hr
  · simpa only [he] using hs
  · simpa using hf
  · simpa using ho

theorem uniform_sum_run (k : ℕ) (xs : List CompetitorValidity.Estimate)
    (ambient : Fin 94 → List Bool) (hv : ∀ a∈xs,a.Valid k)
    (hstore : Store (CompetitorSumWidth.width xs.length k) CompetitorSumWidth.zero
      (words (CompetitorSumWidth.width xs.length k) xs) ambient) :
    ∃ r out,runFrom loopProgram (loopBudget (CompetitorSumWidth.width xs.length k) xs.length)
        (RepeatMachine.cfg 0 (cfg bodyProgram.start 0 ambient) xs.length 1)=some r ∧
      r.steps≤loopBudget (CompetitorSumWidth.width xs.length k) xs.length ∧
      r.final=RepeatMachine.cfg 3 (cfg bodyProgram.start
        (words (CompetitorSumWidth.width xs.length k) xs).length out) xs.length 1 ∧
      Store (CompetitorSumWidth.width xs.length k) (folded CompetitorSumWidth.zero xs)
        (words (CompetitorSumWidth.width xs.length k) xs) out ∧
      (folded CompetitorSumWidth.zero xs).value=(xs.map CompetitorValidity.Estimate.value).sum := by
  obtain ⟨r,out,hr,hs,hf,ho,hv'⟩ := sum_loop_run (CompetitorSumWidth.width xs.length k) CompetitorSumWidth.zero xs ambient
    (CompetitorSumWidth.uniform_trace k xs hv) hstore
  refine ⟨r,out,hr,hs,hf,ho,?_⟩
  have hz : CompetitorSumWidth.zero.value=0 := by norm_num [CompetitorSumWidth.zero,CompetitorValidity.Estimate.value]
  simpa only [hz,zero_add] using hv'

end NearCubicWires.RepairOrdinary.CompetitorSumFold

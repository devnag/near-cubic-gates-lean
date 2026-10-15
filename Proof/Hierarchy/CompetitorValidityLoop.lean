import Proof.Hierarchy.CompetitorValidityBody

/-! Whole ordinary validity-record loop. Failed comparisons halt immediately;
successful iterations reuse the same bounded scalar workspace and leave the
global stream cursor at the next record. The physical list driver is reset
on exhaustion, and every entry, return and reset is charged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (scanned : Fin 71 → Bool) := scanned 65
noncomputable def loopProgram := RepeatMachine.machine recordProgram accepted
def words (b : ℕ) (xs : List Comparison) := xs.flatMap (fun a => a.word b)
def loopBudget (b n : ℕ) := n*(recordBudget b+3)+3

theorem loop_driver_run (b : ℕ) (xs : List Comparison) (total pos : ℕ) (pre suffix : List Bool)
    (ambient : Fin 71 → List Bool) (hn : pos+xs.length=total)
    (hv : ∀ a∈xs,a.Valid b) (hstore : Store b (pre++words b xs++suffix) ambient) :
    ∃ r,runFrom loopProgram (xs.length*(recordBudget b+2)+total+3)
        (RepeatMachine.cfg 0 (cfg recordProgram.start pre.length ambient) total (pos+1))=some r ∧
      r.steps≤xs.length*(recordBudget b+2)+total+3 ∧
      (r.final.control=RepeatMachine.phaseCode _ 3 ↔ ∀ a∈xs,a.passes) := by
  induction xs generalizing pos pre ambient with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust recordProgram accepted
      (cfg recordProgram.start pre.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,by simpa [loopProgram] using hr,by simpa using hs.le,?_⟩
    simp [hf,RepeatMachine.cfg,controlConfig]
  | cons a xs ih =>
    have ha := hv a (by simp)
    obtain ⟨body,hbody,hhead,hnext,hflag,hsteps⟩ := record_run b a pre (words b xs++suffix) ambient ha
      (by simpa [words,List.append_assoc] using hstore)
    have hp := RepeatMachine.iteration recordProgram accepted
      (cfg recordProgram.start pre.length ambient) total pos body rfl (by simp only [List.length_cons] at hn; omega) hbody
    have haccepted : accepted body.final.control body.final.scanned=true ↔ a.passes := by
      simpa [accepted,Configuration.scanned,hhead,heads] using hflag
    cases hacc : accepted body.final.control body.final.scanned with
    | false =>
      have hno : ¬a.passes := by
        intro hyes
        have he := haccepted.mpr hyes
        rw [hacc] at he
        contradiction
      simp only [hacc,Bool.false_eq_true,if_false] at hp
      obtain ⟨r,hr,hf,hs⟩ := hp.run
        (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
      have htime : body.steps+2≤(a::xs).length*(recordBudget b+2)+total+3 := by
        simp only [List.length_cons]
        nlinarith
      have hmore := runFrom_moreFuel loopProgram (body.steps+2)
        ((a::xs).length*(recordBudget b+2)+total+3-(body.steps+2)) _ r hr
      rw [Nat.add_sub_of_le htime] at hmore
      refine ⟨r,hmore,hs.le.trans htime,?_⟩
      simp [hf,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode,hno]
    | true =>
      have hyes : a.passes := haccepted.mp hacc
      simp only [hacc,if_true] at hp
      have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
          RepeatMachine.cfg 0 (cfg recordProgram.start (pre++a.word b).length body.final.tapes) total (pos+2) := by
        apply configuration_ext
        · rfl
        · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hhead,cfg,List.length_append,
            record_length,Nat.add_assoc]
        · rfl
      rw [hend] at hp
      obtain ⟨tail,htail,hts,htf⟩ := ih (pos+1) (pre++a.word b) body.final.tapes
        (by simp only [List.length_cons] at hn; omega)
        (fun c hc => hv c (by simp [hc]))
        (by simpa [List.append_assoc] using hnext)
      have htail' : runFrom loopProgram (xs.length*(recordBudget b+2)+total+3)
          (RepeatMachine.cfg 0 (cfg recordProgram.start (pre++a.word b).length body.final.tapes) total (pos+2))=some tail := by
        simpa only [Nat.add_assoc] using htail
      rcases hp with ⟨space,hprefix⟩
      obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
      have htime : (body.steps+2)+(xs.length*(recordBudget b+2)+total+3)≤
          (a::xs).length*(recordBudget b+2)+total+3 := by
        simp only [List.length_cons]
        nlinarith
      have hmore := runFrom_moreFuel loopProgram _
        ((a::xs).length*(recordBudget b+2)+total+3-((body.steps+2)+(xs.length*(recordBudget b+2)+total+3))) _ r hr
      rw [Nat.add_sub_of_le htime] at hmore
      refine ⟨r,hmore,?_,?_⟩
      · rw [hs]
        simp only [List.length_cons]
        nlinarith
      · rw [hf,htf]
        simp [hyes]

theorem validity_loop_run (b : ℕ) (xs : List Comparison) (ambient : Fin 71 → List Bool)
    (hv : ∀ a∈xs,a.Valid b) (hstore : Store b (words b xs) ambient) :
    ∃ r,runFrom loopProgram (loopBudget b xs.length)
        (RepeatMachine.cfg 0 (cfg recordProgram.start 0 ambient) xs.length 1)=some r ∧
      r.steps≤loopBudget b xs.length ∧
      (r.final.control=RepeatMachine.phaseCode _ 3 ↔ ∀ a∈xs,a.passes) := by
  have h := loop_driver_run b xs xs.length 0 [] [] ambient (by omega) hv (by simpa using hstore)
  have he : xs.length*(recordBudget b+2)+xs.length+3=loopBudget b xs.length := by
    unfold loopBudget
    ring
  simpa only [he,List.length_nil,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.CompetitorValidity

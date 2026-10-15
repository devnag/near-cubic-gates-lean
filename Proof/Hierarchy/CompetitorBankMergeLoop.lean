import Proof.Hierarchy.CompetitorBankMergeBody

/-! One actual n sentinel drives all aligned original cells. Source cursors
stay streaming through both fields of every cell; each local erase is paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWord oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Pair := Cell × Cell
def leftWords (w : ℕ) (xs : List Pair) := oldWords w (xs.map Prod.fst)
def rightWords (w : ℕ) (xs : List Pair) := oldWords w (xs.map Prod.snd)
def mergedCells (xs : List Pair) := xs.map (fun x => merged x.1 x.2)
def mergedWords (w : ℕ) (xs : List Pair) := oldWords w (mergedCells xs)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 27 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine bodyProgram accepted
def loopBudget (w n : ℕ) := n*(bodyBudget w+3)+3

theorem loop_driver_run (w : ℕ) (xs : List Pair) (total pos : ℕ)
    (preA suffixA preB suffixB out : List Bool) (ambient : Fin 27 → List Bool)
    (hpos : pos+xs.length=total) (hv : ∀ a∈xs,Valid w a.1 a.2)
    (hstore : Store w (preA++leftWords w xs++suffixA) (preB++rightWords w xs++suffixB) out ambient) :
    ∃ r output,runFrom loopProgram (xs.length*(bodyBudget w+2)+total+3)
      (RepeatMachine.cfg 0 (cfg bodyProgram.start preA.length preB.length out.length ambient) total (pos+1))=some r ∧
      r.steps≤xs.length*(bodyBudget w+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3
        (cfg bodyProgram.start (preA.length+(leftWords w xs).length) (preB.length+(rightWords w xs).length)
          (out++mergedWords w xs).length output) total 1 ∧
      Store w (preA++leftWords w xs++suffixA) (preB++rightWords w xs++suffixB) (out++mergedWords w xs) output := by
  induction xs generalizing pos preA preB out ambient with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust bodyProgram accepted
      (cfg bodyProgram.start preA.length preB.length out.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,ambient,by simpa [loopProgram] using hr,by simpa using hs.le,?_,?_⟩
    · simpa [leftWords,rightWords,oldWords,mergedWords,mergedCells] using hf
    · simpa [leftWords,rightWords,oldWords,mergedWords,mergedCells] using hstore
  | cons a xs ih =>
    obtain ⟨body,hbody,hbs,hbh,hbt⟩ := body_run w a.1 a.2 preA (leftWords w xs++suffixA)
      preB (rightWords w xs++suffixB) out ambient
      (by simpa [leftWords,rightWords,oldWords,List.append_assoc] using hstore) (hv a (by simp))
    have iteration := RepeatMachine.iteration bodyProgram accepted
      (cfg bodyProgram.start preA.length preB.length out.length ambient) total pos body rfl
      (by simp only [List.length_cons] at hpos; omega) hbody
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg bodyProgram.start (preA++oldWord w a.1).length (preB++oldWord w a.2).length
          (out++oldWord w (merged a.1 a.2)).length body.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hbh,cfg,oldWord,
          CompetitorPlane.pairWord,List.length_append,two_mul]
      · rfl
    rw [hend] at iteration
    obtain ⟨tail,output,htail,hts,htf,hto⟩ := ih (pos+1) (preA++oldWord w a.1) (preB++oldWord w a.2)
      (out++oldWord w (merged a.1 a.2)) body.final.tapes
      (by simp only [List.length_cons] at hpos; omega) (fun c hc => hv c (by simp [hc]))
      (by simpa only [List.append_assoc] using hbt)
    have htail' : runFrom loopProgram (xs.length*(bodyBudget w+2)+total+3)
        (RepeatMachine.cfg 0 (cfg bodyProgram.start (preA++oldWord w a.1).length (preB++oldWord w a.2).length
          (out++oldWord w (merged a.1 a.2)).length body.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(xs.length*(bodyBudget w+2)+total+3)≤
        (a::xs).length*(bodyBudget w+2)+total+3 := by simp only [List.length_cons]; nlinarith
    have hmore := runFrom_moreFuel loopProgram _
      ((a::xs).length*(bodyBudget w+2)+total+3-((body.steps+2)+(xs.length*(bodyBudget w+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,output,hmore,?_,?_,?_⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf]
      simp [leftWords,rightWords,oldWords,mergedWords,mergedCells,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [leftWords,rightWords,oldWords,mergedWords,mergedCells,List.append_assoc] using hto

theorem loop_run (w : ℕ) (xs : List Pair) (suffixA suffixB : List Bool) (ambient : Fin 27 → List Bool)
    (hv : ∀ a∈xs,Valid w a.1 a.2)
    (hstore : Store w (leftWords w xs++suffixA) (rightWords w xs++suffixB) [] ambient) :
    ∃ r out,runFrom loopProgram (loopBudget w xs.length)
      (RepeatMachine.cfg 0 (cfg bodyProgram.start 0 0 0 ambient) xs.length 1)=some r ∧
      r.steps≤loopBudget w xs.length ∧
      r.final=RepeatMachine.cfg 3
        (cfg bodyProgram.start (leftWords w xs).length (rightWords w xs).length (mergedWords w xs).length out) xs.length 1 ∧
      Store w (leftWords w xs++suffixA) (rightWords w xs++suffixB) (mergedWords w xs) out := by
  obtain ⟨r,out,hr,hs,hf,ho⟩ := loop_driver_run w xs xs.length 0 [] suffixA [] suffixB [] ambient
    (by omega) hv (by simpa using hstore)
  have he : xs.length*(bodyBudget w+2)+xs.length+3=loopBudget w xs.length := by unfold loopBudget; ring
  exact ⟨r,out,by simpa only [he,List.length_nil] using hr,
    by simpa only [he] using hs,by simpa using hf,by simpa using ho⟩

end NearCubicWires.RepairOrdinary.CompetitorBankMerge

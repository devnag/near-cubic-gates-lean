import Proof.Hierarchy.CompetitorResidueTableBody
import Proof.Hierarchy.CompetitorPlaneLoop

/-! One physical n-driver traverses every original row-major P/N cell.
Only local scratch is cleared per cell; source/output cursors are streaming. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWord oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (w : ℕ) (a : Cell) := a.positive<2^w ∧ a.negative<2^w
def residueWord (w q : ℕ) (a : Cell) := binary q (CompetitorSignedResidue.residue w q a.positive a.negative)
def residueWords (w q : ℕ) (xs : List Cell) := xs.flatMap (residueWord w q)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 27 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine bodyProgram accepted
def loopBudget (w q n : ℕ) := n*(bodyBudget w q+3)+3

theorem loop_driver_run (w q : ℕ) (xs : List Cell) (total pos : ℕ)
    (pre suffix output : List Bool) (ambient : Fin 27 → List Bool)
    (hpos : pos+xs.length=total) (hq : q≤w) (hv : ∀ a∈xs,Valid w a)
    (hstore : Store w q (pre++oldWords w xs++suffix) output ambient) :
    ∃ r out,runFrom loopProgram (xs.length*(bodyBudget w q+2)+total+3)
      (RepeatMachine.cfg 0 (cfg bodyProgram.start pre.length output.length ambient) total (pos+1))=some r ∧
      r.steps≤xs.length*(bodyBudget w q+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3
        (cfg bodyProgram.start (pre.length+(oldWords w xs).length)
          (output++residueWords w q xs).length out) total 1 ∧
      Store w q (pre++oldWords w xs++suffix) (output++residueWords w q xs) out := by
  induction xs generalizing pos pre output ambient with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust bodyProgram accepted
      (cfg bodyProgram.start pre.length output.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,ambient,by simpa [loopProgram] using hr,by simpa using hs.le,?_,?_⟩
    · simpa [oldWords,residueWords] using hf
    · simpa [oldWords,residueWords] using hstore
  | cons a xs ih =>
    have ha := hv a (by simp)
    obtain ⟨body,hbody,hbs,hbh,hbt⟩ := body_run w q a.positive a.negative
      pre (oldWords w xs++suffix) output ambient
      (by simpa [oldWords,oldWord,List.append_assoc] using hstore) ha.1 ha.2 hq
    have iteration := RepeatMachine.iteration bodyProgram accepted
      (cfg bodyProgram.start pre.length output.length ambient) total pos body rfl
      (by simp only [List.length_cons] at hpos; omega) hbody
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg bodyProgram.start (pre++oldWord w a).length
          (output++residueWord w q a).length body.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hbh,cfg,oldWord,residueWord,
          CompetitorPlane.pairWord,List.length_append,two_mul]
      · rfl
    rw [hend] at iteration
    obtain ⟨tail,out,htail,hts,htf,hto⟩ := ih (pos+1) (pre++oldWord w a)
      (output++residueWord w q a) body.final.tapes
      (by simp only [List.length_cons] at hpos; omega) (fun c hc => hv c (by simp [hc]))
      (by simpa [oldWord,residueWord,List.append_assoc] using hbt)
    have htail' : runFrom loopProgram (xs.length*(bodyBudget w q+2)+total+3)
        (RepeatMachine.cfg 0 (cfg bodyProgram.start (pre++oldWord w a).length
          (output++residueWord w q a).length body.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(xs.length*(bodyBudget w q+2)+total+3)≤
        (a::xs).length*(bodyBudget w q+2)+total+3 := by simp only [List.length_cons]; nlinarith
    have hmore := runFrom_moreFuel loopProgram _
      ((a::xs).length*(bodyBudget w q+2)+total+3-((body.steps+2)+(xs.length*(bodyBudget w q+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,out,hmore,?_,?_,?_⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf]
      simp [oldWords,residueWords,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [oldWords,residueWords,List.append_assoc] using hto

theorem loop_run (w q : ℕ) (xs : List Cell) (suffix : List Bool) (ambient : Fin 27 → List Bool)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a)
    (hstore : Store w q (oldWords w xs++suffix) [] ambient) :
    ∃ r out,runFrom loopProgram (loopBudget w q xs.length)
      (RepeatMachine.cfg 0 (cfg bodyProgram.start 0 0 ambient) xs.length 1)=some r ∧
      r.steps≤loopBudget w q xs.length ∧
      r.final=RepeatMachine.cfg 3
        (cfg bodyProgram.start (oldWords w xs).length (residueWords w q xs).length out) xs.length 1 ∧
      Store w q (oldWords w xs++suffix) (residueWords w q xs) out := by
  obtain ⟨r,out,hr,hs,hf,ho⟩ := loop_driver_run w q xs xs.length 0 [] suffix [] ambient
    (by omega) hq hv (by simpa using hstore)
  have he : xs.length*(bodyBudget w q+2)+xs.length+3=loopBudget w q xs.length := by
    unfold loopBudget
    ring
  exact ⟨r,out,by simpa only [he,List.length_nil,Nat.zero_add] using hr,
    by simpa only [he] using hs,by simpa using hf,by simpa using ho⟩

end NearCubicWires.RepairOrdinary.CompetitorResidueTable

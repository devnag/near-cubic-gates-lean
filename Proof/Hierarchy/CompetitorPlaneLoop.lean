import Proof.Hierarchy.CompetitorPlaneBody

/-! Every native product count is consumed in lockstep with the old raw P/N
pair. The physical driver covers the complete plane, including zero cells.
No bound on the global output iteration or on the number of cells by W is used. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cell where
  count : ℕ
  positive : ℕ
  negative : ℕ
structure Cell.Valid (sign : Bool) (b w : ℕ) (bits : List Bool) (a : Cell) : Prop where
  count : a.count<2^b
  positive : a.positive<2^w
  negative : a.negative<2^w
  shift : a.count*2^bits.length<2^w
  addition : a.count*value bits+(if sign then a.negative else a.positive)<2^w
def countWord (b : ℕ) (a : Cell) := binary b a.count
def oldWord (w : ℕ) (a : Cell) := CompetitorPlane.pairWord w a.positive a.negative
def newWord (sign : Bool) (w : ℕ) (bits : List Bool) (a : Cell) :=
  CompetitorPlane.nextWord sign w a.positive a.negative a.count bits
def countWords (b : ℕ) (xs : List Cell) := xs.flatMap (countWord b)
def oldWords (w : ℕ) (xs : List Cell) := xs.flatMap (oldWord w)
def newWords (sign : Bool) (w : ℕ) (bits : List Bool) (xs : List Cell) := xs.flatMap (newWord sign w bits)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 27 → Bool) := true
noncomputable def planeProgram (sign : Bool) := RepeatMachine.machine (bodyProgram sign) accepted
def planeBudget (w n : ℕ) := n*(bodyBudget w+3)+3

theorem plane_driver_run (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (total pos : ℕ) (preCount tailCount preOld tailOld output : List Bool) (ambient : Fin 27 → List Bool)
    (hpos : pos+xs.length=total) (hb : b≤w) (hbits : bits.length≤w)
    (hv : ∀ a∈xs,a.Valid sign b w bits)
    (hstore : Store b w bits (preCount++countWords b xs++tailCount)
      (preOld++oldWords w xs++tailOld) output ambient) :
    ∃ r out,runFrom (planeProgram sign) (xs.length*(bodyBudget w+2)+total+3)
        (RepeatMachine.cfg 0 (cfg (bodyProgram sign).start preCount.length preOld.length output.length ambient)
          total (pos+1))=some r ∧
      r.steps≤xs.length*(bodyBudget w+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3
        (cfg (bodyProgram sign).start (preCount.length+(countWords b xs).length)
          (preOld.length+(oldWords w xs).length) (output++newWords sign w bits xs).length out) total 1 ∧
      Store b w bits (preCount++countWords b xs++tailCount)
        (preOld++oldWords w xs++tailOld) (output++newWords sign w bits xs) out := by
  induction xs generalizing pos preCount preOld output ambient with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust (bodyProgram sign) accepted
      (cfg (bodyProgram sign).start preCount.length preOld.length output.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,ambient,by simpa [planeProgram] using hr,by simpa using hs.le,?_,?_⟩
    · simpa [countWords,oldWords,newWords] using hf
    · simpa [countWords,oldWords,newWords] using hstore
  | cons a xs ih =>
    have ha := hv a (by simp)
    obtain ⟨body,hbody,hbs,hbh,hbt⟩ := body_run sign b w a.count a.positive a.negative bits
      preCount (countWords b xs++tailCount) preOld (oldWords w xs++tailOld) output ambient
      (by simpa [countWords,oldWords,countWord,oldWord,List.append_assoc] using hstore)
      hb ha.count ha.positive ha.negative hbits ha.shift ha.addition
    have iteration := RepeatMachine.iteration (bodyProgram sign) accepted
      (cfg (bodyProgram sign).start preCount.length preOld.length output.length ambient)
      total pos body rfl (by simp only [List.length_cons] at hpos; omega) hbody
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg (bodyProgram sign).start (preCount++countWord b a).length
          (preOld++oldWord w a).length (output++newWord sign w bits a).length body.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hbh,cfg,countWord,oldWord,newWord,
          CompetitorPlane.pairWord,List.length_append,two_mul]
      · rfl
    rw [hend] at iteration
    obtain ⟨tail,out,htail,hts,htf,hto⟩ := ih (pos+1) (preCount++countWord b a) (preOld++oldWord w a)
      (output++newWord sign w bits a) body.final.tapes
      (by simp only [List.length_cons] at hpos; omega) (fun c hc => hv c (by simp [hc]))
      (by simpa [countWord,oldWord,newWord,List.append_assoc] using hbt)
    have htail' : runFrom (planeProgram sign) (xs.length*(bodyBudget w+2)+total+3)
        (RepeatMachine.cfg 0 (cfg (bodyProgram sign).start (preCount++countWord b a).length
          (preOld++oldWord w a).length (output++newWord sign w bits a).length body.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(xs.length*(bodyBudget w+2)+total+3)≤
        (a::xs).length*(bodyBudget w+2)+total+3 := by simp only [List.length_cons]; nlinarith
    have hmore := runFrom_moreFuel (planeProgram sign) _
      ((a::xs).length*(bodyBudget w+2)+total+3-((body.steps+2)+(xs.length*(bodyBudget w+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,out,hmore,?_,?_,?_⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf]
      simp [countWords,oldWords,newWords,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [countWords,oldWords,newWords,List.append_assoc] using hto

theorem plane_run (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell) (ambient : Fin 27 → List Bool)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits)
    (hstore : Store b w bits (countWords b xs) (oldWords w xs) [] ambient) :
    ∃ r out,runFrom (planeProgram sign) (planeBudget w xs.length)
        (RepeatMachine.cfg 0 (cfg (bodyProgram sign).start 0 0 0 ambient) xs.length 1)=some r ∧
      r.steps≤planeBudget w xs.length ∧
      r.final=RepeatMachine.cfg 3
        (cfg (bodyProgram sign).start (countWords b xs).length (oldWords w xs).length
          (newWords sign w bits xs).length out) xs.length 1 ∧
      Store b w bits (countWords b xs) (oldWords w xs) (newWords sign w bits xs) out := by
  obtain ⟨r,out,hr,hs,hf,ho⟩ := plane_driver_run sign b w bits xs xs.length 0 [] [] [] [] [] ambient
    (by omega) hb hbits hv (by simpa using hstore)
  have he : xs.length*(bodyBudget w+2)+xs.length+3=planeBudget w xs.length := by unfold planeBudget; ring
  exact ⟨r,out,by simpa only [he,List.length_nil,Nat.zero_add] using hr,
    by simpa only [he] using hs,by simpa using hf,by simpa using ho⟩

end NearCubicWires.RepairOrdinary.CompetitorPlaneStream

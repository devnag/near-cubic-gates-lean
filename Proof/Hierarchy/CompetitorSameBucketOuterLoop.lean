import Proof.Hierarchy.CompetitorSameBucketOuterBody

/-! A second physical B counter loads each successive left record from the
original packet. Each inner B scan returns its right-bank cursor before the
next left record; the global source is never rewound per pair. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketOuterLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
open CompetitorSameBucketPackets (word width)
open CompetitorSameBucketCandidate (State Fits words)
open CompetitorSameBucketLeftLoad (cfg heads tapes)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def last (old : Option KeyLoop.Record) : List (Option KeyLoop.Record) → Option KeyLoop.Record
  | [] => old
  | a::xs => last a xs
def emissions (r : Request) (coefficient : ℤ) (xs ys : List (Option KeyLoop.Record)) :=
  xs.flatMap (fun left => CompetitorSameBucketCandidate.emissions r coefficient left ys)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 45 → Bool) := true
noncomputable def machine := RepeatMachine.machine CompetitorSameBucketOuterBody.machine accepted
def budget (r : Request) (cap a b : ℕ) := a*(CompetitorSameBucketOuterBody.budget r cap b+3)+3

theorem driver_run (r : Request) (cap : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xs ys : List (Option KeyLoop.Record)) (total pos : ℕ) (pre suffix rightSuffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hpos : pos+xs.length=total) (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (hx : ∀ a∈xs,Fits r a) (hy : ∀ a∈ys,Fits r a)
    (hstate : State r cap coefficient old (words r ys++rightSuffix) out ambient) :
    ∃ b output,runFrom machine (xs.length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3)
      (RepeatMachine.cfg 0
        (cfg CompetitorSameBucketOuterBody.machine.start pre.length out.length ambient (H r) ys.length
          (pre++words r xs++suffix) (List.replicate cap false)) total (pos+1))=some b ∧
      b.steps≤xs.length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3 ∧
      b.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketOuterBody.machine.start (pre.length+(words r xs).length)
          (out++emissions r coefficient xs ys).length output (H r) ys.length
          (pre++words r xs++suffix) (List.replicate cap false)) total 1 ∧
      State r cap coefficient (last old xs) (words r ys++rightSuffix) (out++emissions r coefficient xs ys) output := by
  induction xs generalizing pos pre old out ambient with
  | nil =>
    have he : pos=total := by simpa using hpos
    subst pos
    obtain ⟨b,hb,bf,bs⟩ := (RepeatMachine.exhaust CompetitorSameBucketOuterBody.machine accepted
      (cfg CompetitorSameBucketOuterBody.machine.start pre.length out.length ambient (H r) ys.length
        (pre++words r []++suffix) (List.replicate cap false)) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨b,ambient,by simpa [machine] using hb,by simpa using bs.le,
      by simpa [words,emissions] using bf,by simpa [last,emissions] using hstate⟩
  | cons a xs ih =>
    obtain ⟨one,mid,hone,os,oh,ot,ostate⟩ := CompetitorSameBucketOuterBody.body_run r cap coefficient old a ys pre
      (words r xs++suffix) rightSuffix out (List.replicate cap false) ambient hc hp (hx a (by simp)) hy (by simp) hstate
    have hone' : runFrom CompetitorSameBucketOuterBody.machine (CompetitorSameBucketOuterBody.budget r cap ys.length)
        (cfg CompetitorSameBucketOuterBody.machine.start pre.length out.length ambient (H r) ys.length
          (pre++words r (a::xs)++suffix) (List.replicate cap false))=some one := by
      simpa only [words,List.flatMap_cons,List.append_assoc] using hone
    have iteration := RepeatMachine.iteration CompetitorSameBucketOuterBody.machine accepted
      (cfg CompetitorSameBucketOuterBody.machine.start pre.length out.length ambient (H r) ys.length
        (pre++words r (a::xs)++suffix) (List.replicate cap false)) total pos one rfl
      (by simp only [List.length_cons] at hpos; omega) hone'
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 one.final total (pos+2)=RepeatMachine.cfg 0
        (cfg CompetitorSameBucketOuterBody.machine.start (pre++word r a).length
          (out++CompetitorSameBucketCandidate.emissions r coefficient a ys).length mid (H r) ys.length
          ((pre++word r a)++words r xs++suffix) (List.replicate cap false)) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,oh,cfg,List.length_append,
          CompetitorSameBucketPackets.word_length]
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ot,cfg,List.append_assoc]
    rw [hend] at iteration
    obtain ⟨tail,output,htail,ts,tf,tailState⟩ := ih (old := a) (pos := pos+1) (pre := pre++word r a)
      (out := out++CompetitorSameBucketCandidate.emissions r coefficient a ys) (ambient := mid)
      (by simp only [List.length_cons] at hpos; omega) (fun c h => hx c (by simp [h])) ostate
    have ht : runFrom machine (xs.length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketOuterBody.machine.start (pre++word r a).length
          (out++CompetitorSameBucketCandidate.emissions r coefficient a ys).length mid (H r) ys.length
          ((pre++word r a)++words r xs++suffix) (List.replicate cap false)) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,path⟩
    obtain ⟨b,hb,bf,bs,_⟩ := path.followedBy tail ht
    have bound : (one.steps+2)+(xs.length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3)≤
        (a::xs).length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3 := by
      simp only [List.length_cons]; nlinarith
    have more := runFrom_moreFuel machine _
      ((a::xs).length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3-
        ((one.steps+2)+(xs.length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+total+3))) _ b hb
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨b,output,more,?_,?_,?_⟩
    · rw [bs]
      simp only [List.length_cons]
      nlinarith
    · rw [bf,tf]
      simp [words,emissions,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [last,emissions,List.append_assoc] using tailState

theorem loop_run (r : Request) (cap : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xs ys : List (Option KeyLoop.Record)) (pre suffix rightSuffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (hx : ∀ a∈xs,Fits r a) (hy : ∀ a∈ys,Fits r a)
    (hstate : State r cap coefficient old (words r ys++rightSuffix) out ambient) :
    ∃ b output,runFrom machine (budget r cap xs.length ys.length)
      (RepeatMachine.cfg 0
        (cfg CompetitorSameBucketOuterBody.machine.start pre.length out.length ambient (H r) ys.length
          (pre++words r xs++suffix) (List.replicate cap false)) xs.length 1)=some b ∧
      b.steps≤budget r cap xs.length ys.length ∧
      b.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketOuterBody.machine.start (pre.length+(words r xs).length)
          (out++emissions r coefficient xs ys).length output (H r) ys.length
          (pre++words r xs++suffix) (List.replicate cap false)) xs.length 1 ∧
      State r cap coefficient (last old xs) (words r ys++rightSuffix) (out++emissions r coefficient xs ys) output := by
  obtain ⟨b,output,hb,bs,bf,bo⟩ := driver_run r cap coefficient old xs ys xs.length 0 pre suffix rightSuffix out ambient
    (by omega) hc hp hx hy hstate
  have he : xs.length*(CompetitorSameBucketOuterBody.budget r cap ys.length+2)+xs.length+3=budget r cap xs.length ys.length := by
    unfold budget; ring
  exact ⟨b,output,by simpa only [he] using hb,by simpa only [he] using bs,bf,bo⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketOuterLoop

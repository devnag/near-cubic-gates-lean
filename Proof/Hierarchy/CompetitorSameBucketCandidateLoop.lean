import Proof.Hierarchy.CompetitorSameBucketCandidateBody

/-! A physical B sentinel executes every candidate against the cached left
record. Only the fixed-width right-bank cursor and contribution cursor
advance; scratch is reset by the checked body on every iteration. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketPackets (word width)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairBits (r : Request) (coefficient : ℤ) (left right : Option KeyLoop.Record) : List Bool :=
  pairOutput r coefficient left right []
def words (r : Request) (xs : List (Option KeyLoop.Record)) := xs.flatMap (word r)
def emissions (r : Request) (coefficient : ℤ) (left : Option KeyLoop.Record) (xs : List (Option KeyLoop.Record)) :=
  xs.flatMap (pairBits r coefficient left)

theorem pair_append (r : Request) (coefficient : ℤ) (left right : Option KeyLoop.Record) (out : List Bool) :
    pairOutput r coefficient left right out=out++pairBits r coefficient left right := by
  cases left <;> cases right <;> simp [pairBits,pairOutput,CompetitorSameBucketPairEmit.output]
  split <;> simp_all
theorem words_length (r : Request) (xs : List (Option KeyLoop.Record)) : (words r xs).length=xs.length*width r := by
  simp [words,List.length_flatMap,CompetitorSameBucketPackets.word_length]

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 41 → Bool) := true
noncomputable def loop := RepeatMachine.machine body accepted
def loopBudget (r : Request) (cap n : ℕ) := n*(budget r cap+3)+3

theorem loop_driver_run (r : Request) (cap : ℕ) (coefficient : ℤ) (left : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (total pos : ℕ) (pre suffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hpos : pos+xs.length=total) (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (hl : Fits r left) (hv : ∀ a∈xs,Fits r a)
    (hstate : State r cap coefficient left (pre++words r xs++suffix) out ambient) :
    ∃ b output,runFrom loop (xs.length*(budget r cap+2)+total+3)
      (RepeatMachine.cfg 0 (cfg body.start pre.length out.length ambient) total (pos+1))=some b ∧
      b.steps≤xs.length*(budget r cap+2)+total+3 ∧
      b.final=RepeatMachine.cfg 3
        (cfg body.start (pre.length+(words r xs).length) (out++emissions r coefficient left xs).length output) total 1 ∧
      State r cap coefficient left (pre++words r xs++suffix) (out++emissions r coefficient left xs) output := by
  induction xs generalizing pos pre out ambient with
  | nil =>
    have he : pos=total := by simpa using hpos
    subst pos
    obtain ⟨b,hb,bf,bs⟩ := (RepeatMachine.exhaust body accepted (cfg body.start pre.length out.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨b,ambient,by simpa [loop] using hb,by simpa using bs.le,
      by simpa [words,emissions] using bf,by simpa [words,emissions] using hstate⟩
  | cons a xs ih =>
    obtain ⟨one,hone,os,oh,ot⟩ := body_run r cap coefficient left a pre (words r xs++suffix) out ambient
      hc hp hl (hv a (by simp)) (by simpa [words,List.append_assoc] using hstate)
    have iteration := RepeatMachine.iteration body accepted (cfg body.start pre.length out.length ambient)
      total pos one rfl (by simp only [List.length_cons] at hpos; omega) hone
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 one.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg body.start (pre++word r a).length
          (out++pairBits r coefficient left a).length one.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,oh,cfg,pair_append,
          List.length_append,CompetitorSameBucketPackets.word_length]
      · rfl
    rw [hend] at iteration
    obtain ⟨tail,output,htail,ts,tf,tailState⟩ := ih (pos+1) (pre++word r a) (out++pairBits r coefficient left a) one.final.tapes
      (by simp only [List.length_cons] at hpos; omega) (fun c h => hv c (by simp [h]))
      (by simpa only [pair_append,List.append_assoc] using ot)
    have ht : runFrom loop (xs.length*(budget r cap+2)+total+3)
        (RepeatMachine.cfg 0 (cfg body.start (pre++word r a).length
          (out++pairBits r coefficient left a).length one.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,path⟩
    obtain ⟨b,hb,bf,bs,_⟩ := path.followedBy tail ht
    have bound : (one.steps+2)+(xs.length*(budget r cap+2)+total+3)≤
        (a::xs).length*(budget r cap+2)+total+3 := by simp only [List.length_cons]; nlinarith
    have more := runFrom_moreFuel loop _
      ((a::xs).length*(budget r cap+2)+total+3-((one.steps+2)+(xs.length*(budget r cap+2)+total+3))) _ b hb
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨b,output,more,?_,?_,?_⟩
    · rw [bs]
      simp only [List.length_cons]
      nlinarith
    · rw [bf,tf]
      simp [words,emissions,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [words,emissions,List.append_assoc] using tailState

theorem loop_run (r : Request) (cap : ℕ) (coefficient : ℤ) (left : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : Fits r left) (hv : ∀ a∈xs,Fits r a)
    (hstate : State r cap coefficient left (pre++words r xs++suffix) out ambient) :
    ∃ b output,runFrom loop (loopBudget r cap xs.length)
      (RepeatMachine.cfg 0 (cfg body.start pre.length out.length ambient) xs.length 1)=some b ∧
      b.steps≤loopBudget r cap xs.length ∧
      b.final=RepeatMachine.cfg 3
        (cfg body.start (pre.length+(words r xs).length) (out++emissions r coefficient left xs).length output) xs.length 1 ∧
      State r cap coefficient left (pre++words r xs++suffix) (out++emissions r coefficient left xs) output := by
  obtain ⟨b,output,hb,bs,bf,bo⟩ := loop_driver_run r cap coefficient left xs xs.length 0 pre suffix out ambient
    (by omega) hc hp hl hv hstate
  have he : xs.length*(budget r cap+2)+xs.length+3=loopBudget r cap xs.length := by unfold loopBudget; ring
  exact ⟨b,output,by simpa only [he] using hb,by simpa only [he] using bs,bf,bo⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate

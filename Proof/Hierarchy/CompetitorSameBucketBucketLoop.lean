import Proof.Hierarchy.CompetitorSameBucketBucketBounds

/-! One actual bucket-count sentinel traverses the complete gate packet.
Every bucket performs its paid D reset/copy and B² candidate work. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
open CompetitorSameBucketCandidate (State Fits words)
open CompetitorSameBucketBucketBody (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def packet (r : Request) (xss : List (List (Option KeyLoop.Record))) := xss.flatMap (words r)
def emissions (r : Request) (coefficient : ℤ) (xss : List (List (Option KeyLoop.Record))) :=
  xss.flatMap (fun xs => CompetitorSameBucketOuterLoop.emissions r coefficient xs xs)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 50 → Bool) := true
noncomputable def machine := RepeatMachine.machine CompetitorSameBucketBucketBody.machine accepted
def budget (r : Request) (d cap b n : ℕ) := n*(CompetitorSameBucketBucketBody.budget r d cap b+3)+3

theorem driver_run (r : Request) (d cap b : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xss : List (List (Option KeyLoop.Record))) (total pos : ℕ) (pre suffix oldRight out : List Bool) (ambient : Fin 41 → List Bool)
    (hpos : pos+xss.length=total) (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (hlen : ∀ xs∈xss,xs.length=b) (hfits : ∀ xs∈xss,∀ a∈xs,Fits r a)
    (hd : 2*(b*CompetitorSameBucketPackets.width r)+4≤d) (targetFit : (ambient 39).length≤d)
    (hstate : State r cap coefficient old oldRight out ambient) :
    ∃ actual output cached rightData,runFrom machine (xss.length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3)
      (RepeatMachine.cfg 0 (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b pre.length out.length ambient
        (pre++packet r xss++suffix) (List.replicate d false)) total (pos+1))=some actual ∧
      actual.steps≤xss.length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3 ∧
      actual.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b (pre.length+(packet r xss).length)
          (out++emissions r coefficient xss).length output (pre++packet r xss++suffix) (List.replicate d false)) total 1 ∧
      State r cap coefficient cached rightData (out++emissions r coefficient xss) output ∧ (output 39).length≤d := by
  induction xss generalizing old oldRight pos pre out ambient with
  | nil =>
    have he : pos=total := by simpa using hpos
    subst pos
    obtain ⟨actual,ha,af,ast⟩ := (RepeatMachine.exhaust CompetitorSameBucketBucketBody.machine accepted
      (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b pre.length out.length ambient
        (pre++packet r []++suffix) (List.replicate d false)) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨actual,ambient,old,oldRight,by simpa [machine] using ha,by simpa using ast.le,
      by simpa [packet,emissions] using af,by simpa [emissions] using hstate,targetFit⟩
  | cons xs xss ih =>
    have hxs := hlen xs (by simp)
    obtain ⟨one,mid,hone,os,oh,ot,ostate,ofit⟩ := CompetitorSameBucketBucketBody.body_run r d cap coefficient old xs pre
      (packet r xss++suffix) oldRight out (List.replicate d false) ambient hc hp (hfits xs (by simp))
      (by rw [CompetitorSameBucketCandidate.words_length,hxs]; exact hd) targetFit (by simp) hstate
    rw [hxs] at hone os ot
    have hone' : runFrom CompetitorSameBucketBucketBody.machine (CompetitorSameBucketBucketBody.budget r d cap b)
        (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b pre.length out.length ambient
          (pre++packet r (xs::xss)++suffix) (List.replicate d false))=some one := by
      simpa only [packet,List.flatMap_cons,List.append_assoc] using hone
    have iteration := RepeatMachine.iteration CompetitorSameBucketBucketBody.machine accepted
      (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b pre.length out.length ambient
        (pre++packet r (xs::xss)++suffix) (List.replicate d false)) total pos one rfl
      (by simp only [List.length_cons] at hpos; omega) hone'
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 one.final total (pos+2)=RepeatMachine.cfg 0
        (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b (pre++words r xs).length
          (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length mid
          ((pre++words r xs)++packet r xss++suffix) (List.replicate d false)) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,oh,cfg,CompetitorSameBucketBucketPrepare.cfg,List.length_append]
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ot,cfg,CompetitorSameBucketBucketPrepare.cfg,List.append_assoc]
    rw [hend] at iteration
    obtain ⟨tail,output,cached,rightData,htail,ts,tf,tailState,tailFit⟩ :=
      ih (old := CompetitorSameBucketOuterLoop.last old xs) (oldRight := ZeroPadding.pad d (words r xs))
        (pos := pos+1) (pre := pre++words r xs) (out := out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs)
        (ambient := mid) (by simp only [List.length_cons] at hpos; omega)
        (fun ys hy => hlen ys (by simp [hy])) (fun ys hy => hfits ys (by simp [hy])) ofit ostate
    have ht : runFrom machine (xss.length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b (pre++words r xs).length
          (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length mid
          ((pre++words r xs)++packet r xss++suffix) (List.replicate d false)) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,path⟩
    obtain ⟨actual,ha,af,ast,_⟩ := path.followedBy tail ht
    have bound : (one.steps+2)+(xss.length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3)≤
        (xs::xss).length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3 := by
      simp only [List.length_cons]; nlinarith
    have more := runFrom_moreFuel machine _
      ((xs::xss).length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3-
        ((one.steps+2)+(xss.length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+total+3))) _ actual ha
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨actual,output,cached,rightData,more,?_,?_,?_,tailFit⟩
    · rw [ast]
      simp only [List.length_cons]
      nlinarith
    · rw [af,tf]
      simp [packet,emissions,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa [emissions,List.append_assoc] using tailState

theorem loop_run (r : Request) (d cap b : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xss : List (List (Option KeyLoop.Record))) (pre suffix oldRight out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (hlen : ∀ xs∈xss,xs.length=b) (hfits : ∀ xs∈xss,∀ a∈xs,Fits r a)
    (hd : 2*(b*CompetitorSameBucketPackets.width r)+4≤d) (targetFit : (ambient 39).length≤d)
    (hstate : State r cap coefficient old oldRight out ambient) :
    ∃ actual output cached rightData,runFrom machine (budget r d cap b xss.length)
      (RepeatMachine.cfg 0 (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b pre.length out.length ambient
        (pre++packet r xss++suffix) (List.replicate d false)) xss.length 1)=some actual ∧
      actual.steps≤budget r d cap b xss.length ∧
      actual.final=RepeatMachine.cfg 3
        (cfg CompetitorSameBucketBucketBody.machine.start d cap (H r) b (pre.length+(packet r xss).length)
          (out++emissions r coefficient xss).length output (pre++packet r xss++suffix) (List.replicate d false)) xss.length 1 ∧
      State r cap coefficient cached rightData (out++emissions r coefficient xss) output ∧ (output 39).length≤d := by
  obtain ⟨actual,output,cached,rightData,ha,ast,af,ao,fit⟩ := driver_run r d cap b coefficient old xss xss.length 0
    pre suffix oldRight out ambient (by omega) hc hp hlen hfits hd targetFit hstate
  have he : xss.length*(CompetitorSameBucketBucketBody.budget r d cap b+2)+xss.length+3=budget r d cap b xss.length := by
    unfold budget; ring
  exact ⟨actual,output,cached,rightData,by simpa only [he] using ha,by simpa only [he] using ast,af,ao,fit⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketLoop

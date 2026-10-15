import Proof.MachineModel.OrdinaryMatrixRightGateBody

/-! The literal Gates-driven loop consumes the consecutive ranked packets,
retains the bounded native bucket workspace, and appends the keyed output
without rewinding either global stream between gates. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open MatrixBatchBucketEndpoints (H)
open MatrixBucketGateLoop (Store)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def state (r : Request) (done : ℕ) (out : List Bool) (s : Store r) : MatrixRightAdvance.Store :=
  ⟨s.boundary,r.bucketSize+1,s.rank,done*r.Buckets,s.upper,s.record,s.clone,out⟩
noncomputable def data (r : Request) (done : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool)
    (unused : Fin 3 → List Bool) (s : Store r) :=
  MatrixRightGateLayout.cfg MatrixRightGateBody.machine.start r (state r done out s) s.packet unused source pos
noncomputable def packets (r : Request) (gs : List (Fin r.Gates)) := gs.flatMap (MatrixScoreRawRanks.output r)
noncomputable def output (r : Request) (gs : List (Fin r.Gates)) := gs.flatMap (MatrixRightNativeCall.output r)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 37 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixRightGateBody.machine accepted
def budget (r : Request) (remaining total : ℕ) := remaining*(MatrixRightGateBody.budget r+2)+total+3

theorem loop_run (r : Request) (gs : List (Fin r.Gates)) (pre suffix out : List Bool)
    (unused : Fin 3 → List Bool) (s : Store r) (total done : ℕ) (hcount : done+gs.length=total)
    (hseq : gs.map Fin.val=List.range' done gs.length) :
    ∃ final : Store r,∃ actual,
      runFrom machine (budget r gs.length total)
        (RepeatMachine.cfg 0 (data r done (pre++packets r gs++suffix) pre.length out unused s) total (done+1))=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (data r total (pre++packets r gs++suffix) (pre.length+(packets r gs).length)
          (out++output r gs) unused final) total 1 ∧ actual.steps≤budget r gs.length total := by
  induction gs generalizing pre out s done with
  | nil =>
    have hdone : done=total := by simpa using hcount
    obtain ⟨actual,hr,hf,hs⟩ := (RepeatMachine.exhaust MatrixRightGateBody.machine accepted
      (data r done (pre++packets r []++suffix) pre.length out unused s) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨s,actual,?_,?_,?_⟩
    · simpa only [machine,budget,List.length_nil,Nat.zero_mul,Nat.zero_add,hdone] using hr
    · simpa only [packets,output,List.flatMap_nil,List.length_nil,Nat.add_zero,List.append_nil,hdone] using hf
    · simpa only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons gate gs ih =>
    have hn : done<total := by simp only [List.length_cons] at hcount; omega
    simp only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] at hseq
    obtain ⟨hgate,hseq⟩ := hseq
    obtain ⟨result,hB,hu,hr,hc,ha,hinner,hout,body,hb,bf,bs⟩ :=
      MatrixRightGateBody.body_run r gate (state r done out s) s.packet unused pre
        (packets r gs++suffix) rfl (by simp only [state,hgate])
        s.upper_fit s.record_fit s.clone_fit s.packet_fit
    let next : Store r := ⟨result.a,result.rank,result.upper,result.record,result.clone,
      MatrixScoreRawRanks.output r gate,hu,hr,hc,MatrixBucketGateLoop.packet_fit r gate⟩
    have hb' : runFrom MatrixRightGateBody.machine (MatrixRightGateBody.budget r)
        (data r done (pre++MatrixScoreRawRanks.output r gate++(packets r gs++suffix)) pre.length out unused s)=some body := hb
    have hstate : result=state r (done+1) (out++MatrixRightNativeCall.output r gate) next := by
      cases result
      simp only [state,next] at *
      simp_all only
    have iteration := RepeatMachine.iteration MatrixRightGateBody.machine accepted
      (data r done (pre++MatrixScoreRawRanks.output r gate++(packets r gs++suffix)) pre.length out unused s)
      total done body rfl hn hb'
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final total (done+2)=
        RepeatMachine.cfg 0
          (data r (done+1) (pre++MatrixScoreRawRanks.output r gate++(packets r gs++suffix))
            (pre.length+(MatrixScoreRawRanks.output r gate).length)
            (out++MatrixRightNativeCall.output r gate) unused next) total (done+2) := by
      rw [bf,hstate]
      rfl
    rw [hi] at iteration
    obtain ⟨final,tail,ht,htf,hts⟩ := ih (pre++MatrixScoreRawRanks.output r gate)
      (out++MatrixRightNativeCall.output r gate) next (done+1)
      (by simp only [List.length_cons] at hcount; omega) hseq
    have ht' : runFrom machine (budget r gs.length total)
        (RepeatMachine.cfg 0
          (data r (done+1) (pre++MatrixScoreRawRanks.output r gate++(packets r gs++suffix))
            (pre.length+(MatrixScoreRawRanks.output r gate).length)
            (out++MatrixRightNativeCall.output r gate) unused next) total (done+2))=some tail := by
      simpa only [List.append_assoc,List.length_append,Nat.add_assoc] using ht
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,haf,has,_⟩ := hprefix.followedBy tail ht'
    have hsmall : body.steps+2+budget r gs.length total≤budget r (gate::gs).length total := by
      unfold budget
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have he := runFrom_moreFuel machine _
      (budget r (gate::gs).length total-(body.steps+2+budget r gs.length total)) _ actual ha
    rw [Nat.add_sub_of_le hsmall] at he
    refine ⟨final,actual,?_,?_,?_⟩
    · simpa only [packets,List.flatMap_cons,List.append_assoc] using he
    · rw [haf,htf]
      simp only [packets,output,List.flatMap_cons,List.length_append,List.append_assoc,Nat.add_assoc]
    · rw [has]
      omega

end NearCubicWires.RepairOrdinary.MatrixRightGateLoop

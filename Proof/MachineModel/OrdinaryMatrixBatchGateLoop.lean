import Proof.MachineModel.OrdinaryMatrixBatchGateStore

/-! Actual Gates-driven repetition of the reusable raw gate producer.
The original cut cursor and complete packet append cursor stay streaming. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.VerifierDecoding
open MatrixBatchGateStore (Store data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cuts (r : Request) (gs : List (Fin r.Gates)) :=
  gs.flatMap (fun gate => cutWord r.p (r.cuts.get gate))
noncomputable def packets (r : Request) (gs : List (Fin r.Gates)) :=
  gs.flatMap (MatrixScoreRawRanks.output r)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 48 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixBatchGateBody.machine accepted
def budget (r : Request) (remaining total : ℕ) :=
  remaining*(MatrixBatchGateStore.budget r+2)+total+3
theorem cuts_nil (r : Request) : cuts r []=[] := rfl
theorem packets_nil (r : Request) : packets r []=[] := rfl
theorem cuts_cons (r : Request) (g : Fin r.Gates) (gs : List (Fin r.Gates)) :
    cuts r (g::gs)=cutWord r.p (r.cuts.get g)++cuts r gs := rfl
theorem packets_cons (r : Request) (g : Fin r.Gates) (gs : List (Fin r.Gates)) :
    packets r (g::gs)=MatrixScoreRawRanks.output r g++packets r gs := rfl

theorem loop_run (r : Request) (gs : List (Fin r.Gates)) (pre suffix out : List Bool)
    (s : Store r) (total done : ℕ) (hcount : done+gs.length=total) :
    ∃ final : Store r,∃ actual,
      runFrom machine (budget r gs.length total)
        (RepeatMachine.cfg 0 (data r (pre++cuts r gs++suffix) pre.length out s) total (done+1))=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (data r (pre++cuts r gs++suffix) (pre.length+(cuts r gs).length) (out++packets r gs) final) total 1 ∧
      actual.steps≤budget r gs.length total := by
  induction gs generalizing pre out s done with
  | nil =>
    have hdone : done=total := by simpa using hcount
    obtain ⟨actual,hr,hf,hs⟩ := (RepeatMachine.exhaust MatrixBatchGateBody.machine accepted
      (data r (pre++cuts r []++suffix) pre.length out s) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨s,actual,?_,?_,?_⟩
    · simpa only [machine,budget,List.length_nil,Nat.zero_mul,Nat.zero_add,hdone] using hr
    · simpa only [cuts_nil,packets_nil,List.length_nil,Nat.add_zero,List.append_nil] using hf
    · simpa only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons gate gs ih =>
    have hn : done<total := by simp only [List.length_cons] at hcount; omega
    obtain ⟨next,body,hb,bh,bt,bs⟩ :=
      MatrixBatchGateStore.step_run r gate pre (cuts r gs++suffix) out s
    have iteration := RepeatMachine.iteration MatrixBatchGateBody.machine accepted
      (data r (pre++cutWord r.p (r.cuts.get gate)++(cuts r gs++suffix)) pre.length out s)
      total done body rfl hn hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final total (done+2)=
        RepeatMachine.cfg 0
          (data r (pre++cutWord r.p (r.cuts.get gate)++(cuts r gs++suffix))
            (pre.length+(cutWord r.p (r.cuts.get gate)).length)
            (out++MatrixScoreRawRanks.output r gate) next) total (done+2) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bh]
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bt]
    rw [hi] at iteration
    obtain ⟨final,tail,ht,htf,hts⟩ := ih (pre++cutWord r.p (r.cuts.get gate))
      (out++MatrixScoreRawRanks.output r gate) next (done+1) (by simp only [List.length_cons] at hcount; omega)
    have ht' : runFrom machine (budget r gs.length total)
        (RepeatMachine.cfg 0
          (data r (pre++cutWord r.p (r.cuts.get gate)++(cuts r gs++suffix))
            (pre.length+(cutWord r.p (r.cuts.get gate)).length)
            (out++MatrixScoreRawRanks.output r gate) next) total (done+2))=some tail := by
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
    · simpa only [cuts_cons,List.append_assoc] using he
    · rw [haf,htf]
      simp only [cuts_cons,packets_cons,List.length_append,List.append_assoc,Nat.add_assoc]
    · rw [has]
      omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateLoop

import Proof.MachineModel.OrdinaryMatrixCoefficientGate

/-! One physical pass extracts all signed coefficients in canonical gate
order. Both global cursors stream; the d-template is reused for each cut,
and the finite Gates driver returns to its sentinel head. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open MatrixCoefficientFields (cfg)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def output (p : ℕ) (cuts : List Cut) := cuts.flatMap (fun c => frame (signMagnitude p c.coefficient))
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 3 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixCoefficientGate.machine accepted
def budget (d p remaining total : ℕ) := remaining*(MatrixCoefficientGate.budget d p+2)+total+3

theorem cut_run (d p : ℕ) (c : Cut) (pre suffix out : List Bool)
    (hl : c.leftWeights.length=d) (hr : c.rightWeights.length=d) : ∃ actual,
    runFrom MatrixCoefficientGate.machine (MatrixCoefficientGate.budget d p)
      (cfg MatrixCoefficientGate.machine.start (pre++cutWord p c++suffix) pre.length d out)=some actual ∧
    actual.final=cfg actual.final.control (pre++cutWord p c++suffix)
      (pre.length+(cutWord p c).length) d (out++frame (signMagnitude p c.coefficient)) ∧
    actual.steps≤MatrixCoefficientGate.budget d p := by
  obtain ⟨actual,ha,hf,hs⟩ := MatrixCoefficientGate.gate_run d p c.leftWeights c.rightWeights
    c.threshold c.coefficient pre suffix out hl hr
  refine ⟨actual,?_,?_,hs⟩
  · simpa only [cutWord,MatrixScoreBatch.fields,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,MatrixScoreCanonical.fields,List.append_assoc] using ha
  · simpa only [cutWord,MatrixScoreBatch.fields,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,MatrixScoreCanonical.fields,List.append_assoc,List.length_append,Nat.add_assoc] using hf

theorem loop_run (d p : ℕ) (cuts : List Cut) (pre suffix out : List Bool) (total done : ℕ)
    (hcount : done+cuts.length=total)
    (hlengths : ∀ c ∈ cuts,c.leftWeights.length=d ∧ c.rightWeights.length=d) : ∃ actual,
    runFrom machine (budget d p cuts.length total)
      (RepeatMachine.cfg 0 (cfg MatrixCoefficientGate.machine.start
        (pre++cuts.flatMap (cutWord p)++suffix) pre.length d out) total (done+1))=some actual ∧
    actual.final=RepeatMachine.cfg 3 (cfg MatrixCoefficientGate.machine.start
      (pre++cuts.flatMap (cutWord p)++suffix) (pre.length+(cuts.flatMap (cutWord p)).length)
      d (out++output p cuts)) total 1 ∧ actual.steps≤budget d p cuts.length total := by
  induction cuts generalizing done pre out with
  | nil =>
    have hd : done=total := by simpa using hcount
    obtain ⟨actual,ha,hf,hs⟩ := (RepeatMachine.exhaust MatrixCoefficientGate.machine accepted
      (cfg MatrixCoefficientGate.machine.start (pre++([] : List Cut).flatMap (cutWord p)++suffix) pre.length d out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [machine,budget,List.length_nil,Nat.zero_mul,Nat.zero_add,hd] using ha
    · simpa only [output,List.flatMap_nil,List.length_nil,Nat.add_zero,List.append_nil] using hf
    · simpa only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons c cuts ih =>
    have hn : done<total := by simp only [List.length_cons] at hcount; omega
    obtain ⟨hl,hr⟩ := hlengths c (by simp)
    obtain ⟨body,hb,bf,bs⟩ := cut_run d p c pre (cuts.flatMap (cutWord p)++suffix) out hl hr
    have iteration := RepeatMachine.iteration MatrixCoefficientGate.machine accepted
      (cfg MatrixCoefficientGate.machine.start (pre++cutWord p c++(cuts.flatMap (cutWord p)++suffix)) pre.length d out)
      total done body rfl hn hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final total (done+2)=
        RepeatMachine.cfg 0 (cfg MatrixCoefficientGate.machine.start
          ((pre++cutWord p c)++cuts.flatMap (cutWord p)++suffix) (pre++cutWord p c).length
          d (out++frame (signMagnitude p c.coefficient))) total (done+2) := by
      rw [bf]
      simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,List.append_assoc,List.length_append]
    rw [hi] at iteration
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++cutWord p c) (out++frame (signMagnitude p c.coefficient)) (done+1)
      (by simp only [List.length_cons] at hcount; omega) (fun c hc => hlengths c (by simp [hc]))
    have ht' : runFrom machine (budget d p cuts.length total)
        (RepeatMachine.cfg 0 (cfg MatrixCoefficientGate.machine.start
          ((pre++cutWord p c)++cuts.flatMap (cutWord p)++suffix) (pre++cutWord p c).length
          d (out++frame (signMagnitude p c.coefficient))) total (done+2))=some tail := by
      simpa only [Nat.add_assoc] using ht
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,hf,hs,_⟩ := hprefix.followedBy tail ht'
    have hsmall : body.steps+2+budget d p cuts.length total≤budget d p (c::cuts).length total := by
      unfold budget
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have he := runFrom_moreFuel machine _
      (budget d p (c::cuts).length total-(body.steps+2+budget d p cuts.length total)) _ actual ha
    rw [Nat.add_sub_of_le hsmall] at he
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [List.flatMap_cons,List.append_assoc] using he
    · rw [hf,tf]
      simp only [output,List.flatMap_cons,List.length_append,List.append_assoc,Nat.add_assoc]
    · rw [hs]
      omega

end NearCubicWires.RepairOrdinary.MatrixCoefficientLoop

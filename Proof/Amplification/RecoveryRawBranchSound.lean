import Proof.Amplification.RecoveryRawBranchWhole

/-! The whole executed raw/default branch proves corrected SAT of its
original code on acceptance; all guard hypotheses are initial physical
state facts that the cold producer must supply. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted_raw_run (x : State) (word : List Bool) (k : Nat) (hx : x.view.Valid)
    (hs : x.view.inner.stream.source=frame word) (hp : x.view.inner.stream.pos=2*k)
    (heval : RecoveryRawSAT.Inv x.view.width x.eval.valuation.cap 0 0 word x.eval)
    (hcode : RecoveryRawViewBody.code x.view=x.eval.code)
    (ht0 : x.view.inner.tags=true)
    (hb : RadixSemantics.value x.view.inner.bound=natBitLength x.eval.code) :
    ∃ r,runFrom machine (budget x.view.width) (cfg x 0 machine.start)=some r ∧
      r.steps ≤ 1073741824*(x.view.width+1)^4 ∧ r.final.heads 93=0 ∧
      r.final.tapes 93=[answer x word k] ∧
      (r.final.tapes 93=[true] → correctedSat x.eval.code=true) := by
  obtain ⟨r,hr,hn,hh,ht⟩ := raw_run x word k hx hs hp heval
  refine ⟨r,hr,hn,hh,ht,?_⟩
  intro ha
  have hanswer : answer x word k=true := List.singleton_inj.mp (ht.symm.trans ha)
  exact answer_sound x word k hx hs hp hcode ht0 hb hanswer

end NearCubicWires.RepairOrdinary.RecoveryRawBranch

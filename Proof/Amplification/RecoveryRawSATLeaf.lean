import Proof.Amplification.RecoveryRawSATGraph

/-! Reuse the complete old clause evaluator and its accepting physical
state. The retained outer code and fixed valuation parameters stay paired
with that actual output for the next clause call. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resultState (x : State) (word : List Bool)
    (out : RecoveryClauseEvaluation.ClauseResult (prepared x).clause (prepared x).valuation word) : State :=
  ⟨out.state,out.extra,(prepared x).outer⟩

theorem result_valid (x : State) (word : List Bool) (hx : x.Valid word)
    (out : RecoveryClauseEvaluation.ClauseResult (prepared x).clause (prepared x).valuation word) :
    (resultState x word out).Valid word := by
  have hp := prepared_valid x word hx
  exact ⟨out.stateValid,out.extraValid,hp.2.2.1,hp.2.2.2.trans out.width.symm⟩

def accepting (x : State) (word : List Bool) (hx : x.Valid word)
    (hz : RadixSemantics.value x.outer.bits≠0)
    (out : RecoveryClauseEvaluation.ClauseResult (prepared x).clause (prepared x).valuation word) :
    AcceptedResult x word where
  data := resultState x word out
  valid := result_valid x word hx out
  width := out.width.trans (prepared_width x word hx)
  outerBits := rfl
  count := out.count
  committed := out.committed
  cap := out.cap
  result := by
    change out.state.result=answer x word
    rw [out.answer]
    simp only [answer,decide_eq_true hz,Bool.true_and]
    rfl

theorem leaf_trace (x : State) (word : List Bool) (hx : x.Valid word)
    (hz : RadixSemantics.value x.outer.bits≠0) :
    ∃ n output,n ≤ 4194304*(x.width+1)^2+1 ∧ output 27=[leafAnswer x word] ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 3)
        (initialConfiguration clauseMachine (prepared x).tapes))
        (RecoveryCalls.stopped sizes (fun _=>0) output) ∧
      (leafAnswer x word=true → ∃ out : AcceptedResult x word,output=out.data.tapes) := by
  have hp := prepared_valid x word hx
  have hrun := RecoveryClauseEvaluation.clause_run (prepared x).clause (prepared x).valuation word hp.1 hp.2.1
  obtain ⟨r,hr,hb,hh,ht,hout⟩ := hrun
  have hready := (ready_of_run RecoveryClauseEvaluation.machine _ _ r hr hh).embed (prepared x).outer.tapes
  have htrace := hready.stop sizes programs 0 next 3 (by intro q; rfl)
  refine ⟨r.steps+1,Fin.addCases (m:=42) (n:=28) (motive:=fun _=>List Bool) r.final.tapes (prepared x).outer.tapes,
    ?_,ht,htrace,?_⟩
  · change r.steps ≤ 4194304*((prepared x).width+1)^2 at hb
    rw [prepared_width x word hx] at hb
    omega
  · intro ha
    obtain ⟨out,he⟩ := hout ha
    refine ⟨accepting x word hx hz out,?_⟩
    rw [he]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryRawSAT

import Proof.Amplification.RecoveryRawBranchTerminals

/-! Complete continuation after successful raw-syntax validation. The
physical tag/default gate precedes the raw bound gate, and the SAT path
uses the exact capped outer count produced by the frontend. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def checkedCfg (x : State) (total : Nat) :=
  if x.view.inner.tags then
    if x.view.inner.bounded then cfg x total (RecoveryCalls.code sizes 1 evalMachine.start)
    else cfg x total (RecoveryCalls.code sizes 3 (0 : Fin 2))
  else cfg x total (RecoveryCalls.code sizes 2 (0 : Fin 2))

theorem checked_trace (x : State) (word : List Bool) (k : Nat) (hx : x.view.Valid)
    (heval : RecoveryRawSAT.Inv x.view.width x.eval.valuation.cap 0 0 word x.eval)
    (ha : RecoveryRawViewEntry.answer x.view word k=true)
    (hv : (output x word k).view.inner.stream.data.present=true) :
    ∃ n,∃ outHeads : Fin 136→Nat,∃ outTapes : Fin 136→List Bool,n ≤ tailBudget x.view.width ∧
      Timed machine n (checkedCfg (output x word k) (total x word k)) (RecoveryCalls.stopped sizes outHeads outTapes) ∧
      outHeads 93=0 ∧ outTapes 93=[answer x word k] := by
  cases ht : (output x word k).view.inner.tags
  · obtain ⟨n,outHeads,outTapes,hn,h,hh,ho⟩ := default_trace (output x word k) (total x word k) hv
    refine ⟨n,outHeads,outTapes,by unfold tailBudget; omega,?_,hh,?_⟩
    · simp only [checkedCfg,ht,Bool.false_eq_true,ite_false]
      exact h
    · simp only [answer,ha,Bool.true_and,ht,Bool.false_eq_true,ite_false]
      exact ho
  · cases hb : (output x word k).view.inner.bounded
    · obtain ⟨n,outHeads,outTapes,hn,h,hh,ho⟩ := reject_trace
        (cfg (output x word k) (total x word k) (0 : Fin 2)).heads
        (cfg (output x word k) (total x word k) (0 : Fin 2)).tapes x.eval.clause.result rfl rfl
      refine ⟨n,outHeads,outTapes,by unfold tailBudget; omega,?_,hh,?_⟩
      · simp only [checkedCfg,ht,hb,ite_true,Bool.false_eq_true,ite_false]
        exact h
      · simp only [answer,ha,Bool.true_and,ht,ite_true,hb,Bool.false_and]
        exact ho
    · have hn : total x word k ≤ 3*(x.view.width+1) := (total_bound x word k ha).trans hx.2.2.2.2
      obtain ⟨n,outHeads,outTapes,hn',h,hh,ho⟩ := eval_trace (output x word k) x.view.width
        x.eval.valuation.cap (total x word k) word heval hn
      refine ⟨n,outHeads,outTapes,hn',?_,hh,?_⟩
      · simp only [checkedCfg,ht,hb,ite_true]
        exact h
      · simp only [answer,ha,Bool.true_and,ht,ite_true,hb]
        exact ho

end NearCubicWires.RepairOrdinary.RecoveryRawBranch

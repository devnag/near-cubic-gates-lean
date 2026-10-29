import SourceAdapters.Compile.OracleAnswerSelection
import SourceAdapters.Compile.OracleClockStep

/-!
proof of `thm:short-pcp-ours`: the complete charged oracle transition vector. Literal control
selects a retained halt, ordinary action, oracle ask, or failure. One actual
oracle-answer wire is supplied by compileQuery; invalid queries never use it.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def encodeClockOption {p : OrdinaryOracleProgram} {width cap : ℕ} :
    Option (ClockState p width cap) → BitInput (clockBits p width cap)
  | none => fun _ => false
  | some a => a.encode

def clockAnswer {p : OrdinaryOracleProgram} {width cap arity : ℕ}
    (a : ClockState p width cap) (O : BitInput arity → Bool) : Bool :=
  O (fun bit => (queryAddressExpression width bit.val).eval
    (queryWordEncoding width (a.window.unpack.tapes p.queryTape)))

theorem clockAnswer_of_query {p : OrdinaryOracleProgram} {width cap arity : ℕ}
    (a : ClockState p width cap) (O : BitInput arity → Bool) (bits padding : List Bool)
    (hq : a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding) :
    clockAnswer a O=fixedArityOracle O (CanonicalBinary.bitsValue bits) := by
  rw [clockAnswer,hq]
  apply queryAddress_oracle
  rw [←hq]
  exact a.window.unpack_fits.2 _

def clockTransitionExpression (p : OrdinaryOracleProgram) (width cap : ℕ)
    (index : Fin (clockBits p width cap)) : BoolExpr (clockBits p width cap+1) :=
  answerTableSelection p width cap fun state scans =>
    if p.base.machine.halted state then .input (index.castAdd 1) else
      match p.query state with
      | none => match p.base.machine.rule state scans with
        | none => .const false
        | some action => .and (liftClockExpression (localGuardExpression p width cap action))
            (liftClockExpression (localActionExpression p width cap action index))
      | some rule => .and (liftClockExpression (queryGuardExpression p width cap))
          (queryActionExpression p width cap rule index)

/-- Exact semantics of every coordinate of the complete transition. -/
theorem clockTransitionExpression_eval {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) (O : BitInput arity → Bool) (index : Fin (clockBits p width cap)) :
    (clockTransitionExpression p width cap index).eval (answerEncoding a (clockAnswer a O))=
      encodeClockOption (clockAdvance (fixedArityOracle O) p width cap a) index := by
  rw [clockTransitionExpression,answerTableSelection_eval]
  by_cases hh : p.base.machine.halted a.window.view.control=true
  · have hs : clockAdvance (fixedArityOracle O) p width cap a=some a := by simp [clockAdvance,hh]
    simp only [hh,↓reduceIte,BoolExpr.eval,answerEncoding,Fin.addCases_left,hs,encodeClockOption]
  · have hn : p.base.machine.halted a.window.view.control=false := Bool.eq_false_iff.mpr hh
    rw [if_neg hh]
    cases hq : p.query a.window.view.control with
    | none =>
      cases hr : p.base.machine.rule a.window.view.control a.window.unpack.scanned with
      | none =>
        rw [clockAdvance_missing a hn hq hr]
        rfl
      | some action =>
        by_cases hg : (localGuardExpression p width cap action).eval a.encode=true
        · obtain ⟨hp,hfit⟩ := (localGuardExpression_eval p width cap a action).1 hg
          rw [clockAdvance_local a action hn hq hr hp hfit]
          simp only [BoolExpr.eval,liftClockExpression_eval,hg,Bool.true_and,encodeClockOption]
          exact localActionExpression_eval a action hfit hp index
        · have hf : (localGuardExpression p width cap action).eval a.encode=false := Bool.eq_false_iff.mpr hg
          rw [clockAdvance_local_reject a action hn hq hr hf]
          simp only [BoolExpr.eval,liftClockExpression_eval,hf,Bool.false_and,encodeClockOption]
    | some rule =>
      by_cases hg : (queryGuardExpression p width cap).eval a.encode=true
      · obtain ⟨hhead,bits,padding,hword,hcost⟩ := (queryGuardExpression_eval p width cap a).1 hg
        rw [clockAdvance_query a rule bits padding hn hq hhead hword hcost]
        simp only [BoolExpr.eval,liftClockExpression_eval,hg,Bool.true_and,encodeClockOption]
        rw [queryActionExpression_eval a rule (clockAnswer a O) bits padding hword hcost,
          clockAnswer_of_query a O bits padding hword]
      · have hf : (queryGuardExpression p width cap).eval a.encode=false := Bool.eq_false_iff.mpr hg
        rw [clockAdvance_query_reject a rule hn hq hf]
        simp only [BoolExpr.eval,liftClockExpression_eval,hf,Bool.false_and,encodeClockOption]

theorem clockTransitionExpression_dead (p : OrdinaryOracleProgram) (width cap : ℕ)
    (answer : Bool) (index : Fin (clockBits p width cap)) :
    (clockTransitionExpression p width cap index).eval
      (Fin.addCases (fun _ : Fin (clockBits p width cap) => false) (fun _ : Fin 1 => answer))=false :=
  answerTableSelection_dead _ _ _ _ _

end NearCubicGates.Adapters.Compile.OracleExecution

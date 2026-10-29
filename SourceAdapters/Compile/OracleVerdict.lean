import SourceAdapters.Compile.OracleSchedule

/-!
proof of `thm:short-pcp-ours`, Step 4: reject unless the bounded computation has halted
and its allocated output tape is literally frame [true]. The final circuit
bit is the negation of that acceptance condition, including dead executions.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem trueFrame_iff (word : List Bool) :
    word=RepairOrdinary.frame [true] ↔ word.length=3 ∧
      readTapeBit word 0=true ∧ readTapeBit word 1=true ∧ readTapeBit word 2=false := by
  cases word with
  | nil => simp [RepairOrdinary.frame]
  | cons a rest =>
    cases rest with
    | nil => simp [RepairOrdinary.frame]
    | cons b rest =>
      cases rest with
      | nil => simp [RepairOrdinary.frame]
      | cons c rest =>
        cases rest with
        | nil => simp [RepairOrdinary.frame,readTapeBit]
        | cons d rest => simp [RepairOrdinary.frame]

def outputWordExpression (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3≤width) :
    BoolExpr (clockBits p width cap) :=
  .and (.input (clockLengthIndex p.base.outputTape ⟨3,by omega⟩))
    (.and (.input (clockViewIndex (cellIndex p.base.outputTape ⟨0,by omega⟩)))
      (.and (.input (clockViewIndex (cellIndex p.base.outputTape ⟨1,by omega⟩)))
        (.not (.input (clockViewIndex (cellIndex p.base.outputTape ⟨2,by omega⟩))))))

theorem outputWordExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3≤width)
    (a : ClockState p width cap) :
    (outputWordExpression p width cap hw).eval a.encode=
      decide (a.window.unpack.tapes p.base.outputTape=RepairOrdinary.frame [true]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [outputWordExpression,BoolExpr.eval,Bool.and_eq_true,ClockState.encode_length,
    ClockState.encode_view,MachineWindow.encode_cell,decide_eq_true_eq,Fin.ext_iff,
    Bool.not_eq_true',trueFrame_iff,Window.unpack_length]
  rfl

def verdictExpression (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3≤width) :
    BoolExpr (clockBits p width cap) :=
  .not (.and (clockControlSelection p width cap (fun q => .const (p.base.machine.halted q)))
    (outputWordExpression p width cap hw))

theorem verdictExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3≤width)
    (a : ClockState p width cap) :
    (verdictExpression p width cap hw).eval a.encode=
      !(p.base.machine.halted a.window.view.control &&
        decide (a.window.unpack.tapes p.base.outputTape=RepairOrdinary.frame [true])) := by
  simp only [verdictExpression,BoolExpr.eval,clockControlSelection_eval,outputWordExpression_eval]

theorem verdictExpression_dead (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3≤width) :
    (verdictExpression p width cap hw).eval (fun _ => false)=true := by
  simp [verdictExpression,outputWordExpression,BoolExpr.eval]

theorem verdictExpression_request (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (z : BitInput r.ell) :
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega)).eval
      (transitionRounds p (requestWidth r) r.fuel O r.fuel (requestClockState p r z).encode)=
        requestVerdict p r O z := by
  rw [transitionRounds_correct]
  have hr := requestClockRun_eq p r O z
  unfold requestVerdict
  rw [←hr]
  cases hs : clockRounds (fixedArityOracle O) p (requestWidth r) r.fuel r.fuel
      (requestClockState p r z) with
  | none => exact verdictExpression_dead _ _ _ _
  | some a =>
    simp only [Option.bind_some,encodeClockOption,verdictExpression_eval]
    cases hh : p.base.machine.halted a.window.view.control <;> simp

end NearCubicGates.Adapters.Compile.OracleExecution

import SourceAdapters.Compile.OracleClockCharge
import SourceAdapters.Compile.OracleLocalExpressions

/-!
proof of `thm:short-pcp-ours`, Step 4: an oracle answer changes only finite control, while the charged
clock subtracts the literal query cost. Heads, cells and allocated lengths are
preserved. The separate caller guard checks query mode, rewind and affordability.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def queryState {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (rule : OracleReturn p.base.stateCount) (answer : Bool) (cost : ℕ) :
    ClockState p width cap :=
  ⟨Window.pack {a.window.unpack with control:=if answer then rule.onTrue else rule.onFalse}
      ⟨a.window.unpack_fits.1,a.window.unpack_fits.2⟩,
    ⟨a.remaining.val-cost,by have := a.remaining.isLt; omega⟩⟩

theorem queryState_observed {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (rule : OracleReturn p.base.stateCount) (answer : Bool) (cost : ℕ) :
    (queryState a rule answer cost).window.observed=
      {a.window.observed with control:=if answer then rule.onTrue else rule.onFalse} := by
  apply window_representation_unique
    (c := {a.window.unpack with control:=if answer then rule.onTrue else rule.onFalse})
  · have h := MachineWindow.ofConfiguration_represents
      (queryState a rule answer cost).window.unpack (queryState a rule answer cost).window.unpack_fits.1
    change (queryState a rule answer cost).window.observed.Represents
      (Window.pack {a.window.unpack with control:=if answer then rule.onTrue else rule.onFalse}
        ⟨a.window.unpack_fits.1,a.window.unpack_fits.2⟩).unpack at h
    rwa [Window.unpack_pack] at h
  · exact ⟨rfl,fun _ => rfl,fun _ _ => rfl⟩

theorem queryState_lengths {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (rule : OracleReturn p.base.stateCount) (answer : Bool) (cost : ℕ) :
    (queryState a rule answer cost).window.lengths=a.window.lengths := by
  funext tape
  apply Fin.ext
  exact a.window.unpack_length tape

def answerEncoding {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (answer : Bool) : BitInput (clockBits p width cap+1) :=
  Fin.addCases a.encode (fun _ : Fin 1 => answer)

def answerExpression (p : OrdinaryOracleProgram) (width cap : ℕ) : BoolExpr (clockBits p width cap+1) :=
  .input ((0 : Fin 1).natAdd (clockBits p width cap))

def liftClockExpression {p : OrdinaryOracleProgram} {width cap : ℕ}
    (e : BoolExpr (clockBits p width cap)) : BoolExpr (clockBits p width cap+1) :=
  renameExpression (fun i => i.castAdd 1) e

theorem liftClockExpression_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (answer : Bool) (e : BoolExpr (clockBits p width cap)) :
    (liftClockExpression e).eval (answerEncoding a answer)=e.eval a.encode := by
  rw [liftClockExpression,renameExpression_eval]
  simp only [answerEncoding,Fin.addCases_left]

def queryActionExpression (p : OrdinaryOracleProgram) (width cap : ℕ)
    (rule : OracleReturn p.base.stateCount) :
    Fin (clockBits p width cap) → BoolExpr (clockBits p width cap+1) :=
  Fin.addCases
    (Fin.addCases
      (fun state => .or
        (.and (answerExpression p width cap) (.const (decide (rule.onTrue=state))))
        (.and (.not (answerExpression p width cap)) (.const (decide (rule.onFalse=state)))))
      (fun rest => .input ((clockViewIndex (rest.natAdd p.base.stateCount)).castAdd 1)))
    (Fin.addCases
      (fun index => let pair := finProdFinEquiv.symm index
        .input ((clockLengthIndex pair.1 pair.2).castAdd 1))
      (fun target => liftClockExpression (clockRemainingExpression p width cap target)))

theorem queryActionExpression_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (rule : OracleReturn p.base.stateCount) (answer : Bool)
    (bits padding : List Bool)
    (hq : a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding)
    (hc : 2*bits.length+2 ≤ a.remaining.val) (index : Fin (clockBits p width cap)) :
    (queryActionExpression p width cap rule index).eval (answerEncoding a answer)=
      (queryState a rule answer (2*bits.length+2)).encode index := by
  refine Fin.addCases (Fin.addCases ?_ ?_) (Fin.addCases ?_ ?_) index
  · intro state
    simp only [queryActionExpression,Fin.addCases_left,BoolExpr.eval,answerExpression,
      answerEncoding,Fin.addCases_right,ClockState.encode]
    rw [queryState_observed]
    cases answer <;> simp [MachineWindow.encode]
  · intro rest
    simp only [queryActionExpression,Fin.addCases_left,Fin.addCases_right,BoolExpr.eval,answerEncoding]
    change a.encode (clockViewIndex (rest.natAdd p.base.stateCount))=
      (queryState a rule answer (2*bits.length+2)).encode (clockViewIndex (rest.natAdd p.base.stateCount))
    rw [ClockState.encode_view,ClockState.encode_view,queryState_observed]
    simp only [MachineWindow.encode,Fin.addCases_right]
  · intro index
    simp only [queryActionExpression,Fin.addCases_left,Fin.addCases_right,BoolExpr.eval,answerEncoding]
    rw [ClockState.encode_length]
    simp only [ClockState.encode,Fin.addCases_left,Fin.addCases_right,queryState_lengths]
  · intro target
    simp only [queryActionExpression,Fin.addCases_right,liftClockExpression_eval,
      clockRemainingExpression_eval p width cap a target bits padding hq,hc,true_and,
      ClockState.encode,queryState,Fin.ext_iff]

end NearCubicGates.Adapters.Compile.OracleExecution

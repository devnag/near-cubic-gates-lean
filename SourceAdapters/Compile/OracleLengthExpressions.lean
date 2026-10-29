import SourceAdapters.Compile.OracleClockEncoding

/-!
proof of `thm:short-pcp-ours`, Step 4: local writes update allocated length exactly, including writes
of false. The length is max(old length,old head+1); unwritten tapes retain
length. These explicit selectors are polynomial in the finite window width.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def lengthSelection {p : OrdinaryOracleProgram} {width cap : ℕ} (tape : Fin p.base.tapeCount)
    (values : Fin (width+1) → BoolExpr (clockBits p width cap)) : BoolExpr (clockBits p width cap) :=
  anyExpression (List.ofFn fun length => .and (.input (clockLengthIndex tape length)) (values length))

theorem lengthSelection_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (tape : Fin p.base.tapeCount)
    (values : Fin (width+1) → BoolExpr (clockBits p width cap)) :
    (lengthSelection tape values).eval a.encode=(values (a.window.lengths tape)).eval a.encode := by
  apply Bool.eq_iff_iff.mpr
  simp only [lengthSelection,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    BoolExpr.eval,ClockState.encode_length,Bool.and_eq_true,decide_eq_true_eq]
  simp

def clockHeadSelection {p : OrdinaryOracleProgram} {width cap : ℕ} (tape : Fin p.base.tapeCount)
    (values : Fin width → BoolExpr (clockBits p width cap)) : BoolExpr (clockBits p width cap) :=
  anyExpression (List.ofFn fun head => .and (.input (clockViewIndex (headIndex tape head))) (values head))

theorem clockHeadSelection_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (tape : Fin p.base.tapeCount)
    (values : Fin width → BoolExpr (clockBits p width cap)) :
    (clockHeadSelection tape values).eval a.encode=
      (values (a.window.observed.heads tape)).eval a.encode := by
  apply Bool.eq_iff_iff.mpr
  simp [clockHeadSelection,BoolExpr.eval]

def actionLengthExpression {p : OrdinaryOracleProgram} {width cap : ℕ}
    (action : Action p.base.tapeCount p.base.stateCount) (tape : Fin p.base.tapeCount)
    (target : Fin (width+1)) : BoolExpr (clockBits p width cap) :=
  match action.write tape with
  | none => .input (clockLengthIndex tape target)
  | some _ => lengthSelection tape fun length => clockHeadSelection tape fun head =>
      .const (decide (max length.val (head.val+1)=target.val))

theorem actionLengthExpression_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (tape : Fin p.base.tapeCount) (target : Fin (width+1)) :
    (actionLengthExpression action tape target).eval a.encode=
      decide (((applyAction a.window.unpack action).tapes tape).length=target.val) := by
  cases hw : action.write tape with
  | none =>
    simp [actionLengthExpression,hw,BoolExpr.eval,applyAction,Window.unpack_length,Fin.ext_iff]
  | some value =>
    simp only [actionLengthExpression,hw,lengthSelection_eval,clockHeadSelection_eval,BoolExpr.eval,
      applyAction,RepairOrdinary.RecoveryTapeSupport.write_length,Window.unpack_length]
    rfl

theorem lengthSelection_operations {p : OrdinaryOracleProgram} {width cap : ℕ}
    (tape : Fin p.base.tapeCount) (values : Fin (width+1) → BoolExpr (clockBits p width cap))
    (bound : ℕ) (h : ∀ length, expressionOperations (values length) ≤ bound) :
    expressionOperations (lengthSelection tape values) ≤ (width+1)*(bound+2)+1 := by
  have hc := anyExpression_operations
    (List.ofFn fun length => BoolExpr.and (.input (clockLengthIndex tape length)) (values length))
    (bound+1) (by
      intro e he
      obtain ⟨length,rfl⟩ := List.mem_ofFn.mp he
      simp only [expressionOperations]
      have := h length
      omega)
  simpa only [lengthSelection,List.length_ofFn,Nat.add_assoc] using hc

theorem clockHeadSelection_operations {p : OrdinaryOracleProgram} {width cap : ℕ}
    (tape : Fin p.base.tapeCount) (values : Fin width → BoolExpr (clockBits p width cap))
    (bound : ℕ) (h : ∀ head, expressionOperations (values head) ≤ bound) :
    expressionOperations (clockHeadSelection tape values) ≤ width*(bound+2)+1 := by
  have hc := anyExpression_operations
    (List.ofFn fun head => BoolExpr.and (.input (clockViewIndex (headIndex tape head))) (values head))
    (bound+1) (by
      intro e he
      obtain ⟨head,rfl⟩ := List.mem_ofFn.mp he
      simp only [expressionOperations]
      have := h head
      omega)
  simpa only [clockHeadSelection,List.length_ofFn,Nat.add_assoc] using hc

theorem actionLengthExpression_operations {p : OrdinaryOracleProgram} {width cap : ℕ}
    (action : Action p.base.tapeCount p.base.stateCount) (tape : Fin p.base.tapeCount)
    (target : Fin (width+1)) :
    expressionOperations (@actionLengthExpression p width cap action tape target) ≤
      (width+1)*(3*width+3)+1 := by
  unfold actionLengthExpression
  split
  · simp [expressionOperations]
  · apply (lengthSelection_operations tape _ (3*width+1) ?_).trans (by nlinarith)
    intro length
    simpa [Nat.mul_comm] using clockHeadSelection_operations (p := p) (cap := cap) tape
      (fun head => BoolExpr.const (decide (max length.val (head.val+1)=target.val))) 1
      (by intro head; rfl)

end NearCubicGates.Adapters.Compile.OracleExecution

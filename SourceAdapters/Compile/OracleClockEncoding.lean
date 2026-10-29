import SourceAdapters.Compile.OracleClockState
import SourceAdapters.Compile.OracleQueryEncoding
import SourceAdapters.Compile.BoundedRank

/-!
proof of `thm:short-pcp-ours`: polynomial-size finite state wires for the charged schedule.
The old cell/head/control block is followed by allocated-length one-hot wires
and remaining-budget one-hot wires. Query wires are exact selections from this
state. -/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem Window.unpack_length {t s width : ℕ} (a : Window t s width) (tape : Fin t) :
    (a.unpack.tapes tape).length=(a.lengths tape).val := by
  have h : (a.lengths tape).val ≤ width := Nat.le_of_lt_succ (a.lengths tape).isLt
  simp [Window.unpack,h]

/-- Observing the reconstructed literal tape masks all unallocated cells. -/
def Window.observed {t s width : ℕ} (a : Window t s width) : MachineWindow t s width :=
  MachineWindow.ofConfiguration a.unpack a.unpack_fits.1

def clockBits (p : OrdinaryOracleProgram) (width cap : ℕ) :=
  windowBits p.base.tapeCount p.base.stateCount width+(p.base.tapeCount*(width+1)+(cap+1))

def clockViewIndex {p : OrdinaryOracleProgram} {width cap : ℕ}
    (i : Fin (windowBits p.base.tapeCount p.base.stateCount width)) : Fin (clockBits p width cap) :=
  i.castAdd _

def clockLengthIndex {p : OrdinaryOracleProgram} {width cap : ℕ}
    (tape : Fin p.base.tapeCount) (length : Fin (width+1)) : Fin (clockBits p width cap) :=
  ((finProdFinEquiv (tape,length)).castAdd (cap+1)).natAdd _

def clockBudgetIndex {p : OrdinaryOracleProgram} {width cap : ℕ}
    (budget : Fin (cap+1)) : Fin (clockBits p width cap) :=
  (budget.natAdd (p.base.tapeCount*(width+1))).natAdd _

def ClockState.encode {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) : BitInput (clockBits p width cap) :=
  Fin.addCases a.window.observed.encode
    (Fin.addCases
      (fun i => let pair := finProdFinEquiv.symm i
        decide (a.window.lengths pair.1=pair.2))
      (fun budget => decide (a.remaining=budget)))

@[simp] theorem ClockState.encode_view {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (i : Fin (windowBits p.base.tapeCount p.base.stateCount width)) :
    a.encode (clockViewIndex i)=a.window.observed.encode i := by
  simp only [ClockState.encode,clockViewIndex,Fin.addCases_left]

@[simp] theorem ClockState.encode_length {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (tape : Fin p.base.tapeCount) (length : Fin (width+1)) :
    a.encode (clockLengthIndex tape length)=decide (a.window.lengths tape=length) := by
  simp only [ClockState.encode,clockLengthIndex,Fin.addCases_right,Fin.addCases_left,
    Equiv.symm_apply_apply]

@[simp] theorem ClockState.encode_budget {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (budget : Fin (cap+1)) :
    a.encode (clockBudgetIndex budget)=decide (a.remaining=budget) := by
  simp only [ClockState.encode,clockBudgetIndex,Fin.addCases_right]

def queryInputIndex (p : OrdinaryOracleProgram) (width cap : ℕ) :
    Fin (queryWordBits width) → Fin (clockBits p width cap) :=
  Fin.addCases
    (fun position : Fin width => clockViewIndex (cellIndex p.queryTape position))
    (fun length : Fin (width+1) => clockLengthIndex p.queryTape length)

/-- The selected query block preserves both literal cells and stored length. -/
theorem ClockState.encode_query {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) :
    (fun i => a.encode (queryInputIndex p width cap i))=
      queryWordEncoding width (a.window.unpack.tapes p.queryTape) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro position
    simp only [queryInputIndex,Fin.addCases_left,ClockState.encode_view,
      MachineWindow.encode_cell,queryWordEncoding]
    rfl
  · intro length
    simp only [queryInputIndex,Fin.addCases_right,ClockState.encode_length,
      queryWordEncoding,Window.unpack_length,Fin.ext_iff]

def clockPrefixExpression (p : OrdinaryOracleProgram) (width cap count : ℕ) :
    BoolExpr (clockBits p width cap) :=
  renameExpression (queryInputIndex p width cap) (queryPrefixExpression width count)

theorem clockPrefixExpression_eval (p : OrdinaryOracleProgram) (width cap count : ℕ)
    (a : ClockState p width cap) :
    (clockPrefixExpression p width cap count).eval a.encode=
      framePrefix count (a.window.unpack.tapes p.queryTape) := by
  rw [clockPrefixExpression,renameExpression_eval,a.encode_query]
  exact queryPrefixExpression_eval _ _ _ (a.window.unpack_fits.2 _)

theorem renameExpression_operations {n m : ℕ} (rename : Fin n → Fin m) (e : BoolExpr n) :
    expressionOperations (renameExpression rename e)=expressionOperations e := by
  induction e <;> simp_all [renameExpression,expressionOperations]

theorem clockPrefixExpression_operations (p : OrdinaryOracleProgram) (width cap count : ℕ) :
    expressionOperations (clockPrefixExpression p width cap count) ≤ 2*count+2*width+6 := by
  rw [clockPrefixExpression,renameExpression_operations]
  exact queryPrefixExpression_operations _ _

end NearCubicGates.Adapters.Compile.OracleExecution

import SourceAdapters.Compile.OracleChargeExpressions
import SourceAdapters.Compile.OracleClockEncoding
import SourceAdapters.Compile.OracleSubstitution

/-!
proof of `thm:short-pcp-ours`, Step 4: combine finite query-prefix gates and the actual remaining-clock
wires. This is one local formula composition; its explicit quadratic per-bit
bound is independent of the number of simulated rounds. -/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def chargeSubstitution (p : OrdinaryOracleProgram) (width cap : ℕ) :
    Fin (chargeBits width cap) → BoolExpr (clockBits p width cap) :=
  Fin.addCases (fun count : Fin width => clockPrefixExpression p width cap count.val)
    (fun budget : Fin (cap+1) => .input (clockBudgetIndex budget))

theorem chargeSubstitution_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) :
    (fun i => (chargeSubstitution p width cap i).eval a.encode)=
      chargeEncoding width cap (a.window.unpack.tapes p.queryTape) a.remaining := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro count
    simp only [chargeSubstitution,Fin.addCases_left,clockPrefixExpression_eval,chargeEncoding]
  · intro budget
    simp only [chargeSubstitution,Fin.addCases_right,BoolExpr.eval,ClockState.encode_budget,chargeEncoding]

def clockRemainingExpression (p : OrdinaryOracleProgram) (width cap : ℕ) (target : Fin (cap+1)) :
    BoolExpr (clockBits p width cap) :=
  substituteExpression (chargeSubstitution p width cap) (queryRemainingExpression width cap target)

theorem clockRemainingExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) (target : Fin (cap+1)) (bits padding : List Bool)
    (hq : a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding) :
    (clockRemainingExpression p width cap target).eval a.encode=
      decide (2*bits.length+2 ≤ a.remaining.val ∧ a.remaining.val-(2*bits.length+2)=target.val) := by
  rw [clockRemainingExpression,substituteExpression_eval,chargeSubstitution_eval,hq]
  apply queryRemainingExpression_eval
  rw [←hq]
  exact a.window.unpack_fits.2 _

theorem chargeSubstitution_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (i : Fin (chargeBits width cap)) :
    expressionOperations (chargeSubstitution p width cap i) ≤ 4*width+6 := by
  refine Fin.addCases ?_ ?_ i
  · intro count
    simp only [chargeSubstitution,Fin.addCases_left]
    have h := clockPrefixExpression_operations p width cap count.val
    have ht := count.isLt
    omega
  · intro budget
    simp [chargeSubstitution,expressionOperations]

theorem clockRemainingExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (target : Fin (cap+1)) :
    expressionOperations (clockRemainingExpression p width cap target) ≤ (4*width+6)*(6*width+3) := by
  have h := substituteExpression_operations (chargeSubstitution p width cap)
    (queryRemainingExpression width cap target) (4*width+6) (by omega)
    (chargeSubstitution_operations p width cap)
  have hc := queryRemainingExpression_operations width cap target
  have hn := expression_nodes_le_operations (queryRemainingExpression width cap target)
  change expressionOperations (clockRemainingExpression p width cap target) ≤ _ at h
  nlinarith

def clockAffordableExpression (p : OrdinaryOracleProgram) (width cap : ℕ) :
    BoolExpr (clockBits p width cap) :=
  substituteExpression (chargeSubstitution p width cap) (queryAffordableExpression width cap)

theorem clockAffordableExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) (bits padding : List Bool)
    (hq : a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding) :
    (clockAffordableExpression p width cap).eval a.encode=decide (2*bits.length+2 ≤ a.remaining.val) := by
  rw [clockAffordableExpression,substituteExpression_eval,chargeSubstitution_eval,hq]
  apply queryAffordableExpression_eval
  rw [←hq]
  exact a.window.unpack_fits.2 _

end NearCubicGates.Adapters.Compile.OracleExecution

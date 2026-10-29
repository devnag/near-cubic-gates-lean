import SourceAdapters.Compile.BoundedExpression

/-!
proof of `thm:short-pcp-ours`, Step 4: composition of fixed local gate formulas with an explicit size
bound. This substitution is only within one transition formula; successive
computation rounds remain shared DAG references. -/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def substituteExpression {n m : ℕ} (values : Fin n → BoolExpr m) : BoolExpr n → BoolExpr m
  | .const value => .const value
  | .input index => values index
  | .not child => .not (substituteExpression values child)
  | .and left right => .and (substituteExpression values left) (substituteExpression values right)
  | .or left right => .or (substituteExpression values left) (substituteExpression values right)

theorem substituteExpression_eval {n m : ℕ} (values : Fin n → BoolExpr m)
    (e : BoolExpr n) (input : BitInput m) :
    (substituteExpression values e).eval input=e.eval (fun i => (values i).eval input) := by
  induction e <;> simp_all [substituteExpression,BoolExpr.eval]

theorem substituteExpression_operations {n m : ℕ} (values : Fin n → BoolExpr m)
    (e : BoolExpr n) (bound : ℕ) (hpos : 1 ≤ bound)
    (hbound : ∀ i, expressionOperations (values i) ≤ bound) :
    expressionOperations (substituteExpression values e) ≤ bound*e.nodeCount := by
  induction e with
  | const value => simpa [substituteExpression,expressionOperations,BoolExpr.nodeCount] using hpos
  | input index => simpa [substituteExpression,BoolExpr.nodeCount] using hbound index
  | not child ih =>
    simp only [substituteExpression,expressionOperations,BoolExpr.nodeCount]
    nlinarith
  | and left right hl hr =>
    simp only [substituteExpression,expressionOperations,BoolExpr.nodeCount]
    nlinarith
  | or left right hl hr =>
    simp only [substituteExpression,expressionOperations,BoolExpr.nodeCount]
    nlinarith

theorem expression_nodes_le_operations {n : ℕ} (e : BoolExpr n) :
    e.nodeCount ≤ 2*expressionOperations e+1 := by
  induction e with
  | const value => simp [BoolExpr.nodeCount,expressionOperations]
  | input index => simp [BoolExpr.nodeCount,expressionOperations]
  | not child ih => simp only [BoolExpr.nodeCount,expressionOperations]; omega
  | and left right hl hr => simp only [BoolExpr.nodeCount,expressionOperations]; omega
  | or left right hl hr => simp only [BoolExpr.nodeCount,expressionOperations]; omega

end NearCubicGates.Adapters.Compile.OracleExecution

import SourceAdapters.Compile.WitnessRanks
import SourceAdapters.Compile.BoundedExpression

/-!
proof of `lem:multitape-refuter`, Step 3: the actual MSB-first half-open prefix [0,high).
The structural comparator adds at most five gates per witness bit and handles both high = 0 and high beyond 2^n.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def renameExpression {n m : ℕ} (rename : Fin n → Fin m) : BoolExpr n → BoolExpr m
  | .const value => .const value
  | .input index => .input (rename index)
  | .not child => .not (renameExpression rename child)
  | .and left right => .and (renameExpression rename left) (renameExpression rename right)
  | .or left right => .or (renameExpression rename left) (renameExpression rename right)

@[simp] theorem renameExpression_eval {n m : ℕ} (rename : Fin n → Fin m)
    (expression : BoolExpr n) (input : BitInput m) :
    (renameExpression rename expression).eval input = expression.eval (fun i => input (rename i)) := by
  induction expression <;> simp_all [renameExpression, BoolExpr.eval]

@[simp] theorem renameExpression_nodes {n m : ℕ} (rename : Fin n → Fin m)
    (expression : BoolExpr n) : (renameExpression rename expression).nodeCount = expression.nodeCount := by
  induction expression <;> simp_all [renameExpression, BoolExpr.nodeCount]

private theorem rankFold_start (bits : List Bool) (start : ℕ) :
    bits.foldl (fun value bit => 2 * value + if bit then 1 else 0) start =
      start * 2^bits.length + bits.foldl (fun value bit => 2 * value + if bit then 1 else 0) 0 := by
  induction bits generalizing start with
  | nil => simp
  | cons bit rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (2*start + if bit then 1 else 0), ih (2*0 + if bit then 1 else 0), pow_succ]
      ring

/-- The first input bit is the most significant bit in the consumer rank. -/
theorem witnessRank_succ {n : ℕ} (witness : BitInput (n+1)) :
    witnessRank witness = (if witness 0 then 2^n else 0) +
      witnessRank (fun i : Fin n => witness i.succ) := by
  unfold witnessRank
  rw [List.ofFn_succ, List.foldl_cons, rankFold_start]
  simp only [List.length_ofFn, Nat.mul_zero, Nat.zero_add]
  cases witness 0 <;> simp

def rankLessExpression : (n : ℕ) → ℕ → BoolExpr n
  | 0, high => .const (decide (0 < high))
  | n+1, high =>
      if high ≤ 2^n then
        .and (.not (.input 0)) (renameExpression Fin.succ (rankLessExpression n high))
      else
        .or (.not (.input 0))
          (.and (.input 0) (renameExpression Fin.succ (rankLessExpression n (high-2^n))))

/-- Exact strict-prefix membership, including the empty high=0 request. -/
theorem rankLessExpression_correct (n high : ℕ) (witness : BitInput n) :
    (rankLessExpression n high).eval witness = true ↔ witnessRank witness < high := by
  induction n generalizing high with
  | zero => simp [rankLessExpression, BoolExpr.eval, witnessRank]
  | succ n ih =>
      have hr := witnessRank_lt (fun i : Fin n => witness i.succ)
      rw [witnessRank_succ]
      unfold rankLessExpression
      split
      · next hh =>
        simp only [BoolExpr.eval, renameExpression_eval, Bool.and_eq_true, Bool.not_eq_true', ih]
        cases witness 0 with
        | false => simp
        | true => simp; omega
      · next hh =>
        simp only [BoolExpr.eval, renameExpression_eval, Bool.or_eq_true, Bool.and_eq_true,
          Bool.not_eq_true', ih]
        cases witness 0 <;> simp <;> omega

/-- Linear comparator size in the witness length; high is charged in the request word. -/
theorem rankLessExpression_nodes (n high : ℕ) :
    (rankLessExpression n high).nodeCount ≤ 5*n+1 := by
  induction n generalizing high with
  | zero => simp [rankLessExpression, BoolExpr.nodeCount]
  | succ n ih =>
      unfold rankLessExpression
      split <;> simp only [BoolExpr.nodeCount, renameExpression_nodes]
      · have := ih high; omega
      · have := ih (high-2^n); omega

example (n : ℕ) (witness : BitInput n) :
    (rankLessExpression n 0).eval witness = false := by
  apply Bool.eq_false_iff.mpr
  simp [rankLessExpression_correct]

example (n : ℕ) (witness : BitInput n) :
    (rankLessExpression n (2^n)).eval witness = true :=
  (rankLessExpression_correct _ _ _).mpr (witnessRank_lt witness)

end NearCubicGates.Adapters.Compile

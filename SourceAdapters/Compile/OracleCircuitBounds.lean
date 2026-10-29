import SourceAdapters.Compile.OracleCircuit
import SourceAdapters.Compile.OracleExpressionBounds

/-!
proof of `thm:short-pcp-ours`, Step 4: count every node of the concrete shared oracle DAG, including
input, query-address, oracle, local update and final output-test nodes.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem verdictExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3≤width) :
    expressionOperations (verdictExpression p width cap hw) ≤ 3*p.base.stateCount+7 := by
  have h : expressionOperations (clockControlSelection p width cap
      (fun q => .const (p.base.machine.halted q))) ≤ 3*p.base.stateCount+1 := by
    unfold clockControlSelection
    apply (anyExpression_operations _ 2 ?_).trans (by simp [Nat.mul_comm])
    intro e he
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp he
    rfl
  simp only [verdictExpression,outputWordExpression,expressionOperations]
  omega

def clockRoundBound (p : OrdinaryOracleProgram) (width cap arity : ℕ) :=
  arity*(width*(4*width+9)+1)+1+
    clockBits p width cap*clockTransitionBound p.base.tapeCount p.base.stateCount width cap

def requestCircuitBound (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :=
  r.ell+clockBits p (requestWidth r) r.fuel+
    r.fuel*clockRoundBound p (requestWidth r) r.fuel r.ell+3*p.base.stateCount+7

end NearCubicGates.Adapters.Compile.OracleExecution

namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit OracleExecution
set_option autoImplicit false

theorem compileClockRound_added {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (builder : OracleDAGBuilder n arity) (wires : Fin (clockBits p width cap) → LiveWire builder) :
    (compileClockRound p width cap builder wires).extension.suffix.length ≤
      clockRoundBound p width cap arity := by
  let answer := compileQuery builder width (fun i => wires (queryInputIndex p width cap i))
  have ha := compileQuery_added builder width (fun i => wires (queryInputIndex p width cap i))
  have hv := compileVectorOnWires_added_le (clockBits p width cap) answer.final
    (roundAnswerWires wires answer) (clockTransitionExpression p width cap)
    (clockTransitionBound p.base.tapeCount p.base.stateCount width cap)
    (clockTransitionExpression_operations p width cap)
  simp only [compileClockRound,OracleDAGExtension.trans,List.length_append]
  change answer.extension.suffix.length+
    (compileVectorOnWires answer.final (roundAnswerWires wires answer)
      (clockBits p width cap) (clockTransitionExpression p width cap)).extension.suffix.length ≤ _
  exact Nat.add_le_add ha hv

theorem compileClockRounds_added {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap fuel : ℕ)
    (builder : OracleDAGBuilder n arity) (wires : Fin (clockBits p width cap) → LiveWire builder) :
    (compileClockRounds p width cap builder wires fuel).extension.suffix.length ≤
      fuel*clockRoundBound p width cap arity := by
  induction fuel generalizing builder with
  | zero => simp [compileClockRounds,OracleDAGExtension.refl]
  | succ fuel ih =>
    let first := compileClockRound p width cap builder wires
    have hfirst := compileClockRound_added p width cap builder wires
    have hrest := ih first.final first.live
    simp only [compileClockRounds,OracleDAGExtension.trans,List.length_append]
    change first.extension.suffix.length+
      (compileClockRounds p width cap first.final first.live fuel).extension.suffix.length ≤ _
    nlinarith

/-- Explicit node bound for the already-defined concrete circuit family. -/
theorem requestCircuit_size (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (requestCircuit p r).size ≤ requestCircuitBound p r := by
  let start := OracleDAGBuilder.empty r.ell r.ell
  let inputs := compileInputs start r.ell id
  let initial := compileVectorOnWires inputs.final inputs.live
    (clockBits p (requestWidth r) r.fuel) (initialExpression p r)
  let rounds := compileClockRounds p (requestWidth r) r.fuel initial.final initial.live r.fuel
  let verdict := compileOnWires rounds.final rounds.live
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega))
  have hi := compileInputs_added r.ell start id
  have ha := compileVectorOnWires_added_le (clockBits p (requestWidth r) r.fuel)
    inputs.final inputs.live (initialExpression p r) 1 (initialExpression_operations p r)
  have hr := compileClockRounds_added p (requestWidth r) r.fuel r.fuel initial.final initial.live
  have hv := verdictExpression_operations p (requestWidth r) r.fuel (by unfold requestWidth; omega)
  have he := compileOnWires_added rounds.final rounds.live
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega))
  change verdict.final.nodes.length ≤ _
  rw [verdict.extension.length_eq,rounds.extension.length_eq,initial.extension.length_eq,
    inputs.extension.length_eq]
  change 0+inputs.extension.suffix.length+initial.extension.suffix.length+
    rounds.extension.suffix.length+verdict.extension.suffix.length ≤ _
  change inputs.extension.suffix.length=r.ell at hi
  change initial.extension.suffix.length ≤ _ at ha
  change rounds.extension.suffix.length ≤ _ at hr
  change verdict.extension.suffix.length=_ at he
  unfold requestCircuitBound
  omega

end NearCubicGates.Adapters.Compile.OracleExpressions

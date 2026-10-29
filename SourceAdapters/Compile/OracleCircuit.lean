import SourceAdapters.Compile.OracleInitial
import SourceAdapters.Compile.OracleVerdict

/-!
proof of `thm:short-pcp-ours`, Step 4: the concrete MW20 circuit for one bounded
short oracle computation. Input gates, initial formulas, every scheduling
round and the negated literal output test are all actual counted DAG nodes.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.Bindings.MW20
  NearCubicWires.FinitePredicateCircuit OracleExecution
set_option autoImplicit false

def compileInputs {n arity : ℕ} (builder : OracleDAGBuilder n arity) :
    (count : ℕ) → (indices : Fin count → Fin n) →
      CompiledValues builder count (fun i _ input => input (indices i))
  | 0, _ =>
      { final := builder
        extension := OracleDAGExtension.refl builder
        output := Fin.elim0
        correct := fun i => Fin.elim0 i }
  | count+1, indices =>
      let first := compileInput builder (indices 0)
      let rest := compileInputs first.final count (fun i => indices i.succ)
      { final := rest.final
        extension := first.extension.trans rest.extension
        output := Fin.cases (rest.extension.lift first.output) rest.output
        correct := by
          intro index
          refine Fin.cases ?_ ?_ index
          · intro O input
            exact (rest.extension.wireValue_lift O input first.output).trans (first.correct O input)
          · intro i O input
            exact rest.correct i O input }

theorem compileInputs_added {n arity : ℕ} (count : ℕ) (builder : OracleDAGBuilder n arity)
    (indices : Fin count → Fin n) :
    (compileInputs builder count indices).extension.suffix.length=count := by
  induction count generalizing builder with
  | zero => rfl
  | succ count ih =>
    simp [compileInputs,OracleDAGExtension.trans,ih,compileInput,OracleDAGExtension.single]

def requestWire (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    CompiledWire (OracleDAGBuilder.empty r.ell r.ell) (fun O input => requestVerdict p r O input) := by
  let start := OracleDAGBuilder.empty r.ell r.ell
  let inputs := compileInputs start r.ell id
  let initial := compileVectorOnWires inputs.final inputs.live
    (clockBits p (requestWidth r) r.fuel) (initialExpression p r)
  let rounds := compileClockRounds p (requestWidth r) r.fuel initial.final initial.live r.fuel
  let verdict := compileOnWires rounds.final rounds.live
    (verdictExpression p (requestWidth r) r.fuel (by unfold requestWidth; omega))
  refine ⟨verdict.final,inputs.extension.trans (initial.extension.trans
    (rounds.extension.trans verdict.extension)),verdict.output,?_⟩
  intro O input
  rw [verdict.correct]
  congr 1
  change (verdictExpression p (requestWidth r) r.fuel _).eval
    (OracleExecution.transitionRounds p (requestWidth r) r.fuel O r.fuel
      (fun index => (initialExpression p r index).eval input))=_
  rw [show (fun index => (initialExpression p r index).eval input)=
    (requestClockState p r input).encode from funext (initialExpression_eval p r input)]
  exact verdictExpression_request p r O input

def requestCircuit (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    OracleCircuit r.ell r.ell :=
  (requestWire p r).final.finish (requestWire p r).output

theorem requestCircuit_eval (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (input : BitInput r.ell) :
    (requestCircuit p r).eval O input=requestVerdict p r O input := by
  rw [requestCircuit,OracleDAGBuilder.finish_eval,(requestWire p r).correct]
  rfl

/-- The exact semantic conjunct of the fixed bounded-computation join. -/
theorem requestCircuit_false_iff (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (input : BitInput r.ell) :
    (requestCircuit p r).eval O input=false ↔
      OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput input) [true] r.fuel := by
  rw [requestCircuit_eval,requestVerdict_false_iff]

end NearCubicGates.Adapters.Compile.OracleExpressions

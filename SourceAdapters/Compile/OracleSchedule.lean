import SourceAdapters.Compile.OracleTransition
import SourceAdapters.Compile.OracleQueryCircuit

/-!
proof of `thm:short-pcp-ours`, Step 4: iterate the complete finite transition through a shared MW20
DAG. Exactly one oracle gate is emitted per scheduling round, even when its
answer is unused; every gate is counted. Old state values remain references,
so formula trees are never substituted across rounds.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def transitionAnswer {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) (input : BitInput (clockBits p width cap)) : Bool :=
  O (fun bit => (queryAddressExpression width bit.val).eval
    (fun i => input (queryInputIndex p width cap i)))

def transitionVector {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) (input : BitInput (clockBits p width cap)) :
    BitInput (clockBits p width cap) :=
  fun index => (clockTransitionExpression p width cap index).eval
    (Fin.addCases input (fun _ : Fin 1 => transitionAnswer p width cap O input))

theorem transitionVector_correct {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) (a : ClockState p width cap) :
    transitionVector p width cap O a.encode=
      encodeClockOption (clockAdvance (fixedArityOracle O) p width cap a) := by
  have ha : transitionAnswer p width cap O a.encode=clockAnswer a O := by
    rw [transitionAnswer,a.encode_query]
    rfl
  funext index
  simp only [transitionVector,ha]
  exact clockTransitionExpression_eval p width cap a O index

theorem transitionVector_dead {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) :
    transitionVector p width cap O (fun _ => false)=fun _ => false := by
  funext index
  exact clockTransitionExpression_dead p width cap _ index

def transitionRounds {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) : ℕ → BitInput (clockBits p width cap) → BitInput (clockBits p width cap)
  | 0, input => input
  | fuel+1, input => transitionRounds p width cap O fuel (transitionVector p width cap O input)

theorem transitionRounds_dead {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) (fuel : ℕ) :
    transitionRounds p width cap O fuel (fun _ => false)=fun _ => false := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [transitionRounds,transitionVector_dead] using ih

theorem transitionRounds_correct {arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (O : BitInput arity → Bool) (fuel : ℕ) (a : ClockState p width cap) :
    transitionRounds p width cap O fuel a.encode=
      encodeClockOption (clockRounds (fixedArityOracle O) p width cap fuel a) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    simp only [transitionRounds,transitionVector_correct,clockRounds]
    cases hs : clockAdvance (fixedArityOracle O) p width cap a with
    | none => simp [encodeClockOption,transitionRounds_dead]
    | some b => simpa [encodeClockOption] using ih b

end NearCubicGates.Adapters.Compile.OracleExecution

namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit OracleExecution
set_option autoImplicit false

def roundAnswerWires {n arity count : ℕ} {builder : OracleDAGBuilder n arity}
    (wires : Fin count → LiveWire builder) {function : OracleFunction n arity}
    (answer : CompiledWire builder function) : Fin (count+1) → LiveWire answer.final :=
  Fin.addCases (fun i => (wires i).lift answer.extension) (fun _ : Fin 1 => answer.live)

theorem roundAnswerWires_functions {n arity count : ℕ} {builder : OracleDAGBuilder n arity}
    (wires : Fin count → LiveWire builder) {function : OracleFunction n arity}
    (answer : CompiledWire builder function) (O : BitInput arity → Bool) (input : BitInput n) :
    (fun i => (roundAnswerWires wires answer i).function O input)=
      Fin.addCases (fun i => (wires i).function O input) (fun _ : Fin 1 => function O input) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [roundAnswerWires,Fin.addCases_left,LiveWire.lift_function]
  · intro j; simp only [roundAnswerWires,Fin.addCases_right,CompiledWire.live_function]

def compileClockRound {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (builder : OracleDAGBuilder n arity) (wires : Fin (clockBits p width cap) → LiveWire builder) :
    CompiledValues builder (clockBits p width cap)
      (fun index O input => transitionVector p width cap O (fun i => (wires i).function O input) index) := by
  let answer := compileQuery builder width (fun i => wires (queryInputIndex p width cap i))
  let outputs := compileVectorOnWires answer.final (roundAnswerWires wires answer)
    (clockBits p width cap) (clockTransitionExpression p width cap)
  refine ⟨outputs.final,answer.extension.trans outputs.extension,outputs.output,?_⟩
  intro index O input
  rw [outputs.correct]
  simp only [roundAnswerWires_functions]
  rfl

def compileClockRounds {n arity : ℕ} (p : OrdinaryOracleProgram) (width cap : ℕ)
    (builder : OracleDAGBuilder n arity) (wires : Fin (clockBits p width cap) → LiveWire builder) :
    (fuel : ℕ) → CompiledValues builder (clockBits p width cap)
      (fun index O input => OracleExecution.transitionRounds p width cap O fuel (fun i => (wires i).function O input) index)
  | 0 =>
      { final := builder
        extension := OracleDAGExtension.refl builder
        output := fun i => (wires i).output
        correct := fun i O input => (wires i).correct O input }
  | fuel+1 =>
      let first := compileClockRound p width cap builder wires
      let rest := compileClockRounds p width cap first.final first.live fuel
      { final := rest.final
        extension := first.extension.trans rest.extension
        output := rest.output
        correct := rest.correct }

end NearCubicGates.Adapters.Compile.OracleExpressions

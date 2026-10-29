import Proof.Circuits.FinitePredicateCircuit

/-!
proof of `lem:multitape-refuter`, Step 3: compile local transition expressions over existing
live DAG wires. Repeating a bounded transition must retain previous outputs
as wires; substituting expression trees would multiply the size each round.
Compilation on an existing live input vector records exact added-node counts.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.FinitePredicateCircuit

set_option autoImplicit false

/-- Existing inputs cost no new node; each Boolean operation costs one node. -/
def expressionOperations {width : ℕ} : BoolExpr width → ℕ
  | .const _ => 1
  | .input _ => 0
  | .not child => expressionOperations child + 1
  | .and left right | .or left right =>
      expressionOperations left + expressionOperations right + 1

/-- Structural expression lowering with input references into the prior DAG. -/
def compileOnWires {n width : ℕ} (builder : BooleanDAGBuilder n)
    (wires : Fin width → LiveWire builder) :
    (expression : BoolExpr width) →
      CompiledWire builder
        (fun input => expression.eval (fun i => (wires i).function input))
  | .const value => compileConst builder value
  | .input index => (wires index).stationary
  | .not child => (compileOnWires builder wires child).not
  | .and left right =>
      let first := compileOnWires builder wires left
      let second := compileOnWires first.final (fun i => (wires i).lift first.extension) right
      first.andThen second
  | .or left right =>
      let first := compileOnWires builder wires left
      let second := compileOnWires first.final (fun i => (wires i).lift first.extension) right
      first.orThen second

theorem compileOnWires_added {n width : ℕ} (builder : BooleanDAGBuilder n)
    (wires : Fin width → LiveWire builder) (expression : BoolExpr width) :
    (compileOnWires builder wires expression).extension.suffix.length =
      expressionOperations expression := by
  induction expression generalizing builder with
  | const value =>
      simp [compileOnWires, compileConst, BooleanDAGExtension.single, expressionOperations]
  | input index =>
      simp [compileOnWires, LiveWire.stationary, BooleanDAGExtension.refl, expressionOperations]
  | not child ih =>
      simp [compileOnWires, CompiledWire.not, ih, BooleanDAGExtension.trans,
        BooleanDAGExtension.single, expressionOperations]
  | and left right ihl ihr =>
      simp [compileOnWires, CompiledWire.andThen, combineSequential, ihl, ihr,
        BooleanDAGExtension.trans, BooleanDAGExtension.single, expressionOperations]
      omega
  | or left right ihl ihr =>
      simp [compileOnWires, CompiledWire.orThen, combineSequential, ihl, ihr,
        BooleanDAGExtension.trans, BooleanDAGExtension.single, expressionOperations]
      omega

/-- A whole finite vector of previously computed values, with shared nodes. -/
structure CompiledValues {n : ℕ} (prior : BooleanDAGBuilder n) (count : ℕ)
    (functions : Fin count → BoolFunction n) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  output : Fin count → Fin final.nodes.length
  correct : ∀ index input,
    (final.values input)[(output index).val]? = some (functions index input)

def CompiledValues.live {n count : ℕ} {prior : BooleanDAGBuilder n}
    {functions : Fin count → BoolFunction n} (values : CompiledValues prior count functions)
    (index : Fin count) : LiveWire values.final where
  function := functions index
  output := values.output index
  correct := values.correct index

/-- Emit a vector of expressions, retaining every earlier output wire. -/
def compileVectorOnWires {n width : ℕ} (builder : BooleanDAGBuilder n)
    (wires : Fin width → LiveWire builder) :
    (count : ℕ) → (expressions : Fin count → BoolExpr width) →
      CompiledValues builder count
        (fun index input => (expressions index).eval (fun i => (wires i).function input))
  | 0, _ =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        output := Fin.elim0
        correct := fun index => Fin.elim0 index }
  | count + 1, expressions =>
      let first := compileOnWires builder wires (expressions 0)
      let rest := compileVectorOnWires first.final
        (fun i => (wires i).lift first.extension) count (fun i => expressions i.succ)
      { final := rest.final
        extension := first.extension.trans rest.extension
        output := Fin.cases (rest.extension.lift first.output) rest.output
        correct := by
          intro index
          refine Fin.cases ?_ ?_ index
          · intro input
            exact (rest.extension.wireValue_lift input first.output).trans (first.correct input)
          · intro i input
            exact rest.correct i input }

/-- A local transition vector has additive, not multiplicative, DAG growth. -/
theorem compileVectorOnWires_added_le {n width : ℕ} (count : ℕ)
    (builder : BooleanDAGBuilder n) (wires : Fin width → LiveWire builder)
    (expressions : Fin count → BoolExpr width) (bound : ℕ)
    (hbound : ∀ index, expressionOperations (expressions index) ≤ bound) :
    (compileVectorOnWires builder wires count expressions).extension.suffix.length ≤ count * bound := by
  induction count generalizing builder with
  | zero => simp [compileVectorOnWires, BooleanDAGExtension.refl]
  | succ count ih =>
      let first := compileOnWires builder wires (expressions 0)
      have hrest := ih first.final (fun i => (wires i).lift first.extension)
        (fun i => expressions i.succ) (fun i => hbound i.succ)
      have hfirst := hbound 0
      simp only [compileVectorOnWires, BooleanDAGExtension.trans, List.length_append]
      change first.extension.suffix.length +
        (compileVectorOnWires first.final (fun i => (wires i).lift first.extension)
          count (fun i => expressions i.succ)).extension.suffix.length ≤ (count + 1) * bound
      rw [show first.extension.suffix.length = expressionOperations (expressions 0) from
        compileOnWires_added builder wires (expressions 0)]
      nlinarith

end NearCubicGates.Adapters.Compile

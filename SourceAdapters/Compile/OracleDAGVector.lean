import SourceAdapters.Compile.OracleDAGExpression

/-!
proof of `thm:short-pcp-ours`, Step 4: shared vector lowering on the exact MW20 DAG. Each expression
uses prior live references, and the node increase is additive across outputs.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

/-- A whole finite vector of previously computed values, with shared nodes. -/
structure CompiledValues {n arity : ℕ} (prior : OracleDAGBuilder n arity) (count : ℕ)
    (functions : Fin count → OracleFunction n arity) where
  final : OracleDAGBuilder n arity
  extension : OracleDAGExtension prior final
  output : Fin count → Fin final.nodes.length
  correct : ∀ index O input,
    (final.values O input)[(output index).val]? = some (functions index O input)

def CompiledValues.live {n arity count : ℕ} {prior : OracleDAGBuilder n arity}
    {functions : Fin count → OracleFunction n arity} (values : CompiledValues prior count functions)
    (index : Fin count) : LiveWire values.final where
  function := functions index
  output := values.output index
  correct := values.correct index

/-- Emit a vector of expressions, retaining every earlier output wire. -/
def compileVectorOnWires {n arity width : ℕ} (builder : OracleDAGBuilder n arity)
    (wires : Fin width → LiveWire builder) :
    (count : ℕ) → (expressions : Fin count → BoolExpr width) →
      CompiledValues builder count
        (fun index O input => (expressions index).eval (fun i => (wires i).function O input))
  | 0, _ =>
      { final := builder
        extension := OracleDAGExtension.refl builder
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
          · intro O input
            exact (rest.extension.wireValue_lift O input first.output).trans (first.correct O input)
          · intro i O input
            exact rest.correct i O input }

/-- A local transition vector has additive, not multiplicative, DAG growth. -/
theorem compileVectorOnWires_added_le {n arity width : ℕ} (count : ℕ)
    (builder : OracleDAGBuilder n arity) (wires : Fin width → LiveWire builder)
    (expressions : Fin count → BoolExpr width) (bound : ℕ)
    (hbound : ∀ index, expressionOperations (expressions index) ≤ bound) :
    (compileVectorOnWires builder wires count expressions).extension.suffix.length ≤ count * bound := by
  induction count generalizing builder with
  | zero => simp [compileVectorOnWires, OracleDAGExtension.refl]
  | succ count ih =>
      let first := compileOnWires builder wires (expressions 0)
      have hrest := ih first.final (fun i => (wires i).lift first.extension)
        (fun i => expressions i.succ) (fun i => hbound i.succ)
      have hfirst := hbound 0
      simp only [compileVectorOnWires, OracleDAGExtension.trans, List.length_append]
      change first.extension.suffix.length +
        (compileVectorOnWires first.final (fun i => (wires i).lift first.extension)
          count (fun i => expressions i.succ)).extension.suffix.length ≤ (count + 1) * bound
      rw [show first.extension.suffix.length = expressionOperations (expressions 0) from
        compileOnWires_added builder wires (expressions 0)]
      nlinarith

end NearCubicGates.Adapters.Compile.OracleExpressions

import SourceAdapters.Compile.OracleDAGBuilder
import SourceAdapters.Compile.BoundedExpression

/-!
proof of `thm:short-pcp-ours`, Step 4: structural Boolean formulas over existing oracle-DAG wires.
The finite prefix/address formulas reuse current configuration references;
they do not substitute the entire previous computation at each round.
-/
namespace NearCubicGates.Adapters.Compile.OracleExpressions
open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false
abbrev OracleFunction (n arity : ℕ) := (BitInput arity → Bool) → BitInput n → Bool

/-- A wire appended to `prior`, together with its exact value on every input. -/
structure CompiledWire {n arity : ℕ} (prior : OracleDAGBuilder n arity)
    (function : OracleFunction n arity) where
  final : OracleDAGBuilder n arity
  extension : OracleDAGExtension prior final
  output : Fin final.nodes.length
  correct : ∀ O input,
    getElem? (final.values O input) output.val = some (function O input)

/-- A previously compiled value viewed at the current end of the shared DAG. -/
structure LiveWire {n arity : ℕ} (builder : OracleDAGBuilder n arity) where
  function : OracleFunction n arity
  output : Fin builder.nodes.length
  correct : ∀ O input,
    getElem? (builder.values O input) output.val = some (function O input)

/-- An existentially named compiled function.  Structural compilers use this
when a sequence of shared intermediate wires determines the semantic function. -/
structure BuiltWire {n arity : ℕ} (prior : OracleDAGBuilder n arity) where
  function : OracleFunction n arity
  compiled : CompiledWire prior function

def BuiltWire.ofCompiled {n arity : ℕ} {prior : OracleDAGBuilder n arity}
    {function : OracleFunction n arity} (compiled : CompiledWire prior function) :
    BuiltWire prior :=
  ⟨function, compiled⟩

def CompiledWire.live {n arity : ℕ} {prior : OracleDAGBuilder n arity}
    {function : OracleFunction n arity} (wire : CompiledWire prior function) :
    LiveWire wire.final where
  function := function
  output := wire.output
  correct := wire.correct

@[simp] theorem CompiledWire.live_function {n arity : ℕ}
    {prior : OracleDAGBuilder n arity} {function : OracleFunction n arity}
    (wire : CompiledWire prior function) :
    wire.live.function = function :=
  rfl

def BuiltWire.live {n arity : ℕ} {prior : OracleDAGBuilder n arity}
    (wire : BuiltWire prior) : LiveWire wire.compiled.final :=
  wire.compiled.live

@[simp] theorem BuiltWire.live_function {n arity : ℕ}
    {prior : OracleDAGBuilder n arity} (wire : BuiltWire prior) :
    wire.live.function = wire.function :=
  rfl

def LiveWire.stationary {n arity : ℕ} {builder : OracleDAGBuilder n arity}
    (wire : LiveWire builder) :
    CompiledWire builder wire.function where
  final := builder
  extension := OracleDAGExtension.refl builder
  output := wire.output
  correct := wire.correct

def LiveWire.lift {n arity : ℕ}
    {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final)
    (wire : LiveWire prior) : LiveWire final where
  function := wire.function
  output := extension.lift wire.output
  correct := by
    intro O input
    rw [extension.wireValue_lift, wire.correct]

@[simp] theorem LiveWire.lift_function {n arity : ℕ}
    {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final)
    (wire : LiveWire prior) :
    (wire.lift extension).function = wire.function :=
  rfl

def CompiledWire.prepend {n arity : ℕ}
    {first middle : OracleDAGBuilder n arity}
    (initialExtension : OracleDAGExtension first middle)
    {function : OracleFunction n arity}
    (wire : CompiledWire middle function) :
    CompiledWire first function where
  final := wire.final
  extension := initialExtension.trans wire.extension
  output := wire.output
  correct := wire.correct

def compileConst {n arity : ℕ} (prior : OracleDAGBuilder n arity)
    (value : Bool) :
    CompiledWire prior (fun _ _ => value) := by
  let final := prior.appendNode (.const value) trivial
  refine
    { final := final
      extension := OracleDAGExtension.single prior (.const value) trivial
      output := prior.newest (.const value) trivial
      correct := ?_ }
  intro O input
  exact prior.appendNode_newest (.const value) trivial O input

def compileInput {n arity : ℕ} (prior : OracleDAGBuilder n arity)
    (index : Fin n) :
    CompiledWire prior (fun _ input => input index) := by
  let final := prior.appendNode (.input index) trivial
  refine
    { final := final
      extension := OracleDAGExtension.single prior (.input index) trivial
      output := prior.newest (.input index) trivial
      correct := ?_ }
  intro O input
  exact prior.appendNode_newest (.input index) trivial O input

def CompiledWire.not {n arity : ℕ} {prior : OracleDAGBuilder n arity}
    {function : OracleFunction n arity}
    (wire : CompiledWire prior function) :
    CompiledWire prior (fun O input => !(function O input)) := by
  let final :=
    wire.final.appendNode (.not wire.output.val) wire.output.isLt
  refine
    { final := final
      extension :=
        wire.extension.trans
          (OracleDAGExtension.single wire.final
            (.not wire.output.val) wire.output.isLt)
      output :=
        wire.final.newest (.not wire.output.val) wire.output.isLt
      correct := ?_ }
  intro O input
  rw [wire.final.appendNode_newest]
  rw [OracleNode.eval, wire.correct]
  rfl

def combineSequential {n arity : ℕ} {prior : OracleDAGBuilder n arity}
    {leftFunction rightFunction : OracleFunction n arity}
    (operation : Bool → Bool → Bool)
    (node : ℕ → ℕ → OracleNode n arity)
    (nodeWellFormed :
      ∀ {builder : OracleDAGBuilder n arity}
        (left right : Fin builder.nodes.length),
        (node left.val right.val).WellFormedAt builder.nodes.length)
    (nodeEval :
      ∀ (O : BitInput arity → Bool) (input : BitInput n) (values : Array Bool)
        (left right : ℕ),
        (node left right).eval O input values =
          operation (values[left]?.getD false)
            (values[right]?.getD false))
    (left : CompiledWire prior leftFunction)
    (right : CompiledWire left.final rightFunction) :
    CompiledWire prior
      (fun O input => operation (leftFunction O input) (rightFunction O input)) := by
  let liftedLeft := right.extension.lift left.output
  let resultNode := node liftedLeft.val right.output.val
  have hnode :
      resultNode.WellFormedAt right.final.nodes.length :=
    nodeWellFormed liftedLeft right.output
  let final := right.final.appendNode resultNode hnode
  refine
    { final := final
      extension :=
        left.extension.trans <|
          right.extension.trans <|
            OracleDAGExtension.single right.final resultNode hnode
      output := right.final.newest resultNode hnode
      correct := ?_ }
  intro O input
  rw [right.final.appendNode_newest]
  rw [show resultNode.eval O input (right.final.values O input) =
      operation
        ((right.final.values O input)[liftedLeft.val]?.getD false)
        ((right.final.values O input)[right.output.val]?.getD false) by
    exact nodeEval O input (right.final.values O input)
      liftedLeft.val right.output.val]
  rw [right.extension.wireValue_lift O input left.output,
    left.correct, right.correct]
  simp

def CompiledWire.andThen {n arity : ℕ}
    {prior : OracleDAGBuilder n arity}
    {leftFunction rightFunction : OracleFunction n arity}
    (left : CompiledWire prior leftFunction)
    (right : CompiledWire left.final rightFunction) :
    CompiledWire prior
      (fun O input => leftFunction O input && rightFunction O input) :=
  combineSequential (· && ·) OracleNode.and
    (by
      intro builder left right
      exact ⟨left.isLt, right.isLt⟩)
    (by
      intro O input values left right
      rfl)
    left right

def CompiledWire.orThen {n arity : ℕ}
    {prior : OracleDAGBuilder n arity}
    {leftFunction rightFunction : OracleFunction n arity}
    (left : CompiledWire prior leftFunction)
    (right : CompiledWire left.final rightFunction) :
    CompiledWire prior
      (fun O input => leftFunction O input || rightFunction O input) :=
  combineSequential (· || ·) OracleNode.or
    (by
      intro builder left right
      exact ⟨left.isLt, right.isLt⟩)
    (by
      intro O input values left right
      rfl)
    left right


/-- One genuine oracle gate, whose address wires precede it in the DAG. -/
def compileOracle {n arity : ℕ} (prior : OracleDAGBuilder n arity)
    (arguments : Fin arity → LiveWire prior) :
    CompiledWire prior (fun O input => O (fun j => (arguments j).function O input)) := by
  let args := fun j => (arguments j).output.val
  have hf : (OracleNode.oracle args : OracleNode n arity).WellFormedAt prior.nodes.length := fun j => (arguments j).output.isLt
  refine ⟨prior.appendNode (.oracle args) hf,OracleDAGExtension.single _ _ hf,
    prior.newest _ hf,?_⟩
  intro O input
  rw [prior.appendNode_newest]
  simp only [OracleNode.eval]
  congr 2
  funext j
  rw [(arguments j).correct]
  rfl

/-- Existing configuration wires add no node; Boolean operations add one. -/
def compileOnWires {n arity width : ℕ} (builder : OracleDAGBuilder n arity)
    (wires : Fin width → LiveWire builder) :
    (expression : BoolExpr width) →
      CompiledWire builder (fun O input => expression.eval (fun i => (wires i).function O input))
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

theorem compileOnWires_added {n arity width : ℕ} (builder : OracleDAGBuilder n arity)
    (wires : Fin width → LiveWire builder) (expression : BoolExpr width) :
    (compileOnWires builder wires expression).extension.suffix.length = expressionOperations expression := by
  induction expression generalizing builder with
  | const value => simp [compileOnWires,compileConst,OracleDAGExtension.single,expressionOperations]
  | input index => simp [compileOnWires,LiveWire.stationary,OracleDAGExtension.refl,expressionOperations]
  | not child ih =>
      simp [compileOnWires,CompiledWire.not,ih,OracleDAGExtension.trans,
        OracleDAGExtension.single,expressionOperations]
  | and left right ihl ihr =>
      simp [compileOnWires,CompiledWire.andThen,combineSequential,ihl,ihr,
        OracleDAGExtension.trans,OracleDAGExtension.single,expressionOperations]
      omega
  | or left right ihl ihr =>
      simp [compileOnWires,CompiledWire.orThen,combineSequential,ihl,ihr,
        OracleDAGExtension.trans,OracleDAGExtension.single,expressionOperations]
      omega

end NearCubicGates.Adapters.Compile.OracleExpressions

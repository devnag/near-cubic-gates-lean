import Proof.Foundations.BooleanDAGBuilder

/-!
# Shared Boolean-DAG expression compiler

This module builds structural Boolean predicates through the repository's sole
verified append API.  Compilers retain live wires into one shared topological
DAG, and the exact added-node lemmas below support downstream size ledgers.
-/

namespace NearCubicWires.FinitePredicateCircuit

open NearCubicWires

/-- A wire appended to `prior`, together with its exact value on every input. -/
structure CompiledWire {n : ℕ} (prior : BooleanDAGBuilder n)
    (function : BoolFunction n) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  output : Fin final.nodes.length
  correct : ∀ input,
    getElem? (final.values input) output.val = some (function input)

/-- A previously compiled value viewed at the current end of the shared DAG. -/
structure LiveWire {n : ℕ} (builder : BooleanDAGBuilder n) where
  function : BoolFunction n
  output : Fin builder.nodes.length
  correct : ∀ input,
    getElem? (builder.values input) output.val = some (function input)

/-- An existentially named compiled function.  Structural compilers use this
when a sequence of shared intermediate wires determines the semantic function. -/
structure BuiltWire {n : ℕ} (prior : BooleanDAGBuilder n) where
  function : BoolFunction n
  compiled : CompiledWire prior function

def BuiltWire.ofCompiled {n : ℕ} {prior : BooleanDAGBuilder n}
    {function : BoolFunction n} (compiled : CompiledWire prior function) :
    BuiltWire prior :=
  ⟨function, compiled⟩

def CompiledWire.live {n : ℕ} {prior : BooleanDAGBuilder n}
    {function : BoolFunction n} (wire : CompiledWire prior function) :
    LiveWire wire.final where
  function := function
  output := wire.output
  correct := wire.correct

@[simp] theorem CompiledWire.live_function {n : ℕ}
    {prior : BooleanDAGBuilder n} {function : BoolFunction n}
    (wire : CompiledWire prior function) :
    wire.live.function = function :=
  rfl

def BuiltWire.live {n : ℕ} {prior : BooleanDAGBuilder n}
    (wire : BuiltWire prior) : LiveWire wire.compiled.final :=
  wire.compiled.live

@[simp] theorem BuiltWire.live_function {n : ℕ}
    {prior : BooleanDAGBuilder n} (wire : BuiltWire prior) :
    wire.live.function = wire.function :=
  rfl

def LiveWire.stationary {n : ℕ} {builder : BooleanDAGBuilder n}
    (wire : LiveWire builder) :
    CompiledWire builder wire.function where
  final := builder
  extension := BooleanDAGExtension.refl builder
  output := wire.output
  correct := wire.correct

def LiveWire.lift {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (wire : LiveWire prior) : LiveWire final where
  function := wire.function
  output := extension.lift wire.output
  correct := by
    intro input
    rw [extension.wireValue_lift, wire.correct]

@[simp] theorem LiveWire.lift_function {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (wire : LiveWire prior) :
    (wire.lift extension).function = wire.function :=
  rfl

def CompiledWire.prepend {n : ℕ}
    {first middle : BooleanDAGBuilder n}
    (initialExtension : BooleanDAGExtension first middle)
    {function : BoolFunction n}
    (wire : CompiledWire middle function) :
    CompiledWire first function where
  final := wire.final
  extension := initialExtension.trans wire.extension
  output := wire.output
  correct := wire.correct

def compileConst {n : ℕ} (prior : BooleanDAGBuilder n)
    (value : Bool) :
    CompiledWire prior (fun _ => value) := by
  let final := prior.appendNode (.const value) trivial
  refine
    { final := final
      extension := BooleanDAGExtension.single prior (.const value) trivial
      output := prior.newest (.const value) trivial
      correct := ?_ }
  intro input
  exact prior.appendNode_newest (.const value) trivial input

def compileInput {n : ℕ} (prior : BooleanDAGBuilder n)
    (index : Fin n) :
    CompiledWire prior (fun input => input index) := by
  let final := prior.appendNode (.input index) trivial
  refine
    { final := final
      extension := BooleanDAGExtension.single prior (.input index) trivial
      output := prior.newest (.input index) trivial
      correct := ?_ }
  intro input
  exact prior.appendNode_newest (.input index) trivial input

def CompiledWire.not {n : ℕ} {prior : BooleanDAGBuilder n}
    {function : BoolFunction n}
    (wire : CompiledWire prior function) :
    CompiledWire prior (fun input => !(function input)) := by
  let final :=
    wire.final.appendNode (.not wire.output.val) wire.output.isLt
  refine
    { final := final
      extension :=
        wire.extension.trans
          (BooleanDAGExtension.single wire.final
            (.not wire.output.val) wire.output.isLt)
      output :=
        wire.final.newest (.not wire.output.val) wire.output.isLt
      correct := ?_ }
  intro input
  rw [wire.final.appendNode_newest]
  rw [BooleanNode.eval, wire.correct]
  rfl

def combineSequential {n : ℕ} {prior : BooleanDAGBuilder n}
    {leftFunction rightFunction : BoolFunction n}
    (operation : Bool → Bool → Bool)
    (node : ℕ → ℕ → BooleanNode n)
    (nodeWellFormed :
      ∀ {builder : BooleanDAGBuilder n}
        (left right : Fin builder.nodes.length),
        (node left.val right.val).WellFormedAt builder.nodes.length)
    (nodeEval :
      ∀ (input : BitInput n) (values : Array Bool)
        (left right : ℕ),
        (node left right).eval input values =
          operation (values[left]?.getD false)
            (values[right]?.getD false))
    (left : CompiledWire prior leftFunction)
    (right : CompiledWire left.final rightFunction) :
    CompiledWire prior
      (fun input => operation (leftFunction input) (rightFunction input)) := by
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
            BooleanDAGExtension.single right.final resultNode hnode
      output := right.final.newest resultNode hnode
      correct := ?_ }
  intro input
  rw [right.final.appendNode_newest]
  rw [show resultNode.eval input (right.final.values input) =
      operation
        ((right.final.values input)[liftedLeft.val]?.getD false)
        ((right.final.values input)[right.output.val]?.getD false) by
    exact nodeEval input (right.final.values input)
      liftedLeft.val right.output.val]
  rw [right.extension.wireValue_lift input left.output,
    left.correct, right.correct]
  simp

def CompiledWire.andThen {n : ℕ}
    {prior : BooleanDAGBuilder n}
    {leftFunction rightFunction : BoolFunction n}
    (left : CompiledWire prior leftFunction)
    (right : CompiledWire left.final rightFunction) :
    CompiledWire prior
      (fun input => leftFunction input && rightFunction input) :=
  combineSequential (· && ·) BooleanNode.and
    (by
      intro builder left right
      exact ⟨left.isLt, right.isLt⟩)
    (by
      intro input values left right
      rfl)
    left right

def CompiledWire.orThen {n : ℕ}
    {prior : BooleanDAGBuilder n}
    {leftFunction rightFunction : BoolFunction n}
    (left : CompiledWire prior leftFunction)
    (right : CompiledWire left.final rightFunction) :
    CompiledWire prior
      (fun input => leftFunction input || rightFunction input) :=
  combineSequential (· || ·) BooleanNode.or
    (by
      intro builder left right
      exact ⟨left.isLt, right.isLt⟩)
    (by
      intro input values left right
      rfl)
    left right

def compileAnd {n : ℕ} (builder : BooleanDAGBuilder n)
    (left right : LiveWire builder) :
    CompiledWire builder
      (fun input => left.function input && right.function input) :=
  left.stationary.andThen right.stationary

def compileOr {n : ℕ} (builder : BooleanDAGBuilder n)
    (left right : LiveWire builder) :
    CompiledWire builder
      (fun input => left.function input || right.function input) :=
  left.stationary.orThen right.stationary

def compileNot {n : ℕ} (builder : BooleanDAGBuilder n)
    (wire : LiveWire builder) :
    CompiledWire builder (fun input => !(wire.function input)) :=
  wire.stationary.not

def compileAll {n : ℕ} (builder : BooleanDAGBuilder n) :
    (wires : List (LiveWire builder)) →
      CompiledWire builder
        (fun input => wires.all (fun wire => wire.function input))
  | [] => compileConst builder true
  | wire :: rest =>
      let tail := compileAll builder rest
      let lifted := wire.lift tail.extension
      let combined := compileAnd tail.final lifted tail.live
      by
        simpa [lifted, LiveWire.lift, CompiledWire.live] using
          combined.prepend tail.extension

def compileAny {n : ℕ} (builder : BooleanDAGBuilder n) :
    (wires : List (LiveWire builder)) →
      CompiledWire builder
        (fun input => wires.any (fun wire => wire.function input))
  | [] => compileConst builder false
  | wire :: rest =>
      let tail := compileAny builder rest
      let lifted := wire.lift tail.extension
      let combined := compileOr tail.final lifted tail.live
      by
        simpa [lifted, LiveWire.lift, CompiledWire.live] using
          combined.prepend tail.extension

/-- A small expression language for structural predicates.  Compilation is
shared-DAG preserving: callers may keep earlier outputs as live wires instead
of expanding them back into expression trees. -/
inductive BoolExpr (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : BoolExpr n)
  | and (left right : BoolExpr n)
  | or (left right : BoolExpr n)

def BoolExpr.eval {n : ℕ} (input : BitInput n) : BoolExpr n → Bool
  | .const value => value
  | .input index => input index
  | .not child => !(child.eval input)
  | .and left right => left.eval input && right.eval input
  | .or left right => left.eval input || right.eval input

def BoolExpr.nodeCount {n : ℕ} : BoolExpr n → ℕ
  | .const _ | .input _ => 1
  | .not child => child.nodeCount + 1
  | .and left right | .or left right =>
      left.nodeCount + right.nodeCount + 1

def BoolExpr.all {n : ℕ} : List (BoolExpr n) → BoolExpr n
  | [] => .const true
  | expression :: rest => .and expression (BoolExpr.all rest)

def BoolExpr.any {n : ℕ} : List (BoolExpr n) → BoolExpr n
  | [] => .const false
  | expression :: rest => .or expression (BoolExpr.any rest)

@[simp] theorem BoolExpr.eval_all {n : ℕ}
    (expressions : List (BoolExpr n)) (input : BitInput n) :
    (BoolExpr.all expressions).eval input =
      expressions.all (fun expression => expression.eval input) := by
  induction expressions with
  | nil => rfl
  | cons expression rest inductionHypothesis =>
      simp [BoolExpr.all, BoolExpr.eval, inductionHypothesis]

@[simp] theorem BoolExpr.eval_any {n : ℕ}
    (expressions : List (BoolExpr n)) (input : BitInput n) :
    (BoolExpr.any expressions).eval input =
      expressions.any (fun expression => expression.eval input) := by
  induction expressions with
  | nil => rfl
  | cons expression rest inductionHypothesis =>
      simp [BoolExpr.any, BoolExpr.eval, inductionHypothesis]

theorem BoolExpr.nodeCount_all_le {n : ℕ}
    (expressions : List (BoolExpr n)) (bound : ℕ)
    (heach : ∀ expression ∈ expressions,
      expression.nodeCount ≤ bound) :
    (BoolExpr.all expressions).nodeCount ≤
      expressions.length * (bound + 1) + 1 := by
  induction expressions with
  | nil =>
      simp [BoolExpr.all, BoolExpr.nodeCount]
  | cons expression rest inductionHypothesis =>
      simp only [BoolExpr.all, BoolExpr.nodeCount, List.length_cons]
      have hhead := heach expression (by simp)
      have htail := inductionHypothesis (by
        intro item hmember
        exact heach item (by simp [hmember]))
      calc
        expression.nodeCount + (BoolExpr.all rest).nodeCount + 1 ≤
            bound + (rest.length * (bound + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hhead htail) 1
        _ = (rest.length + 1) * (bound + 1) + 1 := by ring

theorem BoolExpr.nodeCount_any_le {n : ℕ}
    (expressions : List (BoolExpr n)) (bound : ℕ)
    (heach : ∀ expression ∈ expressions,
      expression.nodeCount ≤ bound) :
    (BoolExpr.any expressions).nodeCount ≤
      expressions.length * (bound + 1) + 1 := by
  induction expressions with
  | nil =>
      simp [BoolExpr.any, BoolExpr.nodeCount]
  | cons expression rest inductionHypothesis =>
      simp only [BoolExpr.any, BoolExpr.nodeCount, List.length_cons]
      have hhead := heach expression (by simp)
      have htail := inductionHypothesis (by
        intro item hmember
        exact heach item (by simp [hmember]))
      calc
        expression.nodeCount + (BoolExpr.any rest).nodeCount + 1 ≤
            bound + (rest.length * (bound + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hhead htail) 1
        _ = (rest.length + 1) * (bound + 1) + 1 := by ring

def compileExpr {n : ℕ} (builder : BooleanDAGBuilder n) :
    (expression : BoolExpr n) →
      CompiledWire builder expression.eval
  | .const value => compileConst builder value
  | .input index => compileInput builder index
  | .not child =>
      let compiled := compileExpr builder child
      compiled.not
  | .and left right =>
      let compiledLeft := compileExpr builder left
      let compiledRight := compileExpr compiledLeft.final right
      compiledLeft.andThen compiledRight
  | .or left right =>
      let compiledLeft := compileExpr builder left
      let compiledRight := compileExpr compiledLeft.final right
      compiledLeft.orThen compiledRight

/-- One guarded reference into an already compiled shared value table. -/
structure GuardedChoice {n : ℕ} (builder : BooleanDAGBuilder n) where
  condition : BoolExpr n
  value : LiveWire builder

def GuardedChoice.eval {n : ℕ} {builder : BooleanDAGBuilder n}
    (choice : GuardedChoice builder) (input : BitInput n) : Bool :=
  choice.condition.eval input && choice.value.function input

def GuardedChoice.lift {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (choice : GuardedChoice prior) : GuardedChoice final where
  condition := choice.condition
  value := choice.value.lift extension

@[simp] theorem GuardedChoice.lift_eval {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (choice : GuardedChoice prior) (input : BitInput n) :
    (choice.lift extension).eval input = choice.eval input :=
  rfl

def compileGuardedAny {n : ℕ} (builder : BooleanDAGBuilder n) :
    (choices : List (GuardedChoice builder)) →
      CompiledWire builder
        (fun input => choices.any (fun choice => choice.eval input))
  | [] => compileConst builder false
  | choice :: rest =>
      let condition := compileExpr builder choice.condition
      let guarded := compileAnd condition.final condition.live
        (choice.value.lift condition.extension)
      let headExtension := condition.extension.trans guarded.extension
      let liftedRest := rest.map (GuardedChoice.lift headExtension)
      let tail := compileGuardedAny guarded.final liftedRest
      let merged := compileOr tail.final
        (guarded.live.lift tail.extension) tail.live
      let result :=
        merged.prepend (headExtension.trans tail.extension)
      by
        refine
          { final := result.final
            extension := result.extension
            output := result.output
            correct := ?_ }
        intro input
        rw [result.correct]
        congr 1
        change
          (choice.eval input ||
              liftedRest.any (fun lifted => lifted.eval input)) =
            (choice.eval input ||
              rest.any (fun original => original.eval input))
        congr 1
        dsimp only [liftedRest]
        rw [List.any_map]
        apply congrArg
        funext original
        exact GuardedChoice.lift_eval headExtension original input
termination_by choices => choices.length
decreasing_by
  simp only [List.length_map, List.length_cons]
  omega

@[simp] theorem compileExpr_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (expression : BoolExpr n) :
    (compileExpr builder expression).extension.suffix.length =
      expression.nodeCount := by
  induction expression generalizing builder with
  | const value =>
      simp [compileExpr, compileConst, BooleanDAGExtension.single,
        BoolExpr.nodeCount]
  | input index =>
      simp [compileExpr, compileInput, BooleanDAGExtension.single,
        BoolExpr.nodeCount]
  | not child inductionHypothesis =>
      simp [compileExpr, CompiledWire.not, inductionHypothesis,
        BooleanDAGExtension.trans, BooleanDAGExtension.single,
        BoolExpr.nodeCount]
  | and left right leftHypothesis rightHypothesis =>
      simp [compileExpr, CompiledWire.andThen, combineSequential,
        leftHypothesis, rightHypothesis, BooleanDAGExtension.trans,
        BooleanDAGExtension.single, BoolExpr.nodeCount]
      omega
  | or left right leftHypothesis rightHypothesis =>
      simp [compileExpr, CompiledWire.orThen, combineSequential,
        leftHypothesis, rightHypothesis, BooleanDAGExtension.trans,
        BooleanDAGExtension.single, BoolExpr.nodeCount]
      omega

@[simp] theorem compileConst_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (value : Bool) :
    (compileConst builder value).extension.suffix.length = 1 := by
  simp [compileConst, BooleanDAGExtension.single]

@[simp] theorem compileNot_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (wire : LiveWire builder) :
    (compileNot builder wire).extension.suffix.length = 1 := by
  simp [compileNot, LiveWire.stationary, CompiledWire.not,
    BooleanDAGExtension.refl, BooleanDAGExtension.trans,
    BooleanDAGExtension.single]

@[simp] theorem compileAnd_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (left right : LiveWire builder) :
    (compileAnd builder left right).extension.suffix.length = 1 := by
  simp [compileAnd, LiveWire.stationary, CompiledWire.andThen,
    combineSequential, BooleanDAGExtension.trans,
    BooleanDAGExtension.refl, BooleanDAGExtension.single]

@[simp] theorem compileOr_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (left right : LiveWire builder) :
    (compileOr builder left right).extension.suffix.length = 1 := by
  simp [compileOr, LiveWire.stationary, CompiledWire.orThen,
    combineSequential, BooleanDAGExtension.trans,
    BooleanDAGExtension.refl, BooleanDAGExtension.single]

def guardedAnyNodeCount {n : ℕ} {builder : BooleanDAGBuilder n}
    (choices : List (GuardedChoice builder)) : ℕ :=
  match choices with
  | [] => 1
  | choice :: rest =>
      choice.condition.nodeCount + 2 + guardedAnyNodeCount rest

def guardedConditionsNodeCount {n : ℕ} :
    List (BoolExpr n) → ℕ
  | [] => 1
  | condition :: rest =>
      condition.nodeCount + 2 + guardedConditionsNodeCount rest

@[simp] theorem guardedAnyNodeCount_eq_conditions {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (choices : List (GuardedChoice builder)) :
    guardedAnyNodeCount choices =
      guardedConditionsNodeCount
        (choices.map GuardedChoice.condition) := by
  induction choices with
  | nil =>
      rfl
  | cons choice rest inductionHypothesis =>
      simp only [guardedAnyNodeCount, List.map_cons,
        guardedConditionsNodeCount, inductionHypothesis]

@[simp] theorem guardedAnyNodeCount_lift {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (choices : List (GuardedChoice prior)) :
    guardedAnyNodeCount (choices.map (GuardedChoice.lift extension)) =
      guardedAnyNodeCount choices := by
  induction choices with
  | nil =>
      rfl
  | cons choice rest inductionHypothesis =>
      simp only [List.map_cons, guardedAnyNodeCount]
      exact congrArg (choice.condition.nodeCount + 2 + ·)
        inductionHypothesis

@[simp] theorem compileGuardedAny_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (choices : List (GuardedChoice builder)) :
    (compileGuardedAny builder choices).extension.suffix.length =
      guardedAnyNodeCount choices := by
  fun_induction compileGuardedAny
  · simp [guardedAnyNodeCount, compileConst,
      BooleanDAGExtension.single]
  · rename_i builder' choice rest condition guarded headExtension
      liftedRest tail merged result ihTail ihRecursive
    have hcondition :
        condition.extension.suffix.length =
          choice.condition.nodeCount := by
      simpa only [condition] using
        compileExpr_addedNodes builder' choice.condition
    have hguarded :
        guarded.extension.suffix.length = 1 := by
      simpa only [guarded] using
        compileAnd_addedNodes condition.final condition.live
          (choice.value.lift condition.extension)
    have htail :
        tail.extension.suffix.length =
          guardedAnyNodeCount liftedRest := by
      exact ihTail
    have hmerged :
        merged.extension.suffix.length = 1 := by
      simpa only [merged] using
        compileOr_addedNodes tail.final
          (guarded.live.lift tail.extension) tail.live
    have hlifted :
        guardedAnyNodeCount liftedRest =
          guardedAnyNodeCount rest := by
      simpa only [liftedRest] using
        guardedAnyNodeCount_lift headExtension rest
    change
      (((condition.extension.trans guarded.extension).trans
          tail.extension).trans merged.extension).suffix.length =
        choice.condition.nodeCount + 2 +
          guardedAnyNodeCount rest
    simp only [BooleanDAGExtension.trans, List.length_append,
      hcondition, hguarded, htail, hmerged, hlifted]
    omega

end NearCubicWires.FinitePredicateCircuit

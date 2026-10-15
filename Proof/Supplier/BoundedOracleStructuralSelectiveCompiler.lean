import Proof.Circuits.BoundedOracleStructuralFormulaTable

/-!
# Selective bounded-oracle structural compiler

The canonical verifier compiler is append-only.  A pointwise formula emitter
therefore does not need to retain its exponentially large node suffix: it need
only count emitted nodes, remember the node at one requested offset, and retain
the live wire indices required by later compiler steps.  The definitions below
are the proof-level transition system for that streaming implementation.  They
mirror the sole `BooleanDAGBuilder` compiler operation-for-operation; no second
gate grammar or CNF schedule is introduced.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveCompiler

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

/-- Constant-space projection of one append-only builder execution. -/
structure SelectiveState (n : ℕ) where
  target : ℕ
  next : ℕ
  selected : Option (BooleanNode n)

structure SelectiveWire (n : ℕ) where
  state : SelectiveState n
  output : ℕ

structure SelectiveWireList (n : ℕ) where
  state : SelectiveState n
  values : List ℕ

def SelectiveState.empty (n target : ℕ) : SelectiveState n where
  target
  next := 0
  selected := none

/-- The single selective append transition.  Child references are already
absolute append indices, exactly as in `BooleanDAGBuilder`. -/
def SelectiveState.emit {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n) :
    SelectiveWire n :=
  { state :=
      { target := state.target
        next := state.next + 1
        selected :=
          if state.target = state.next then some node else state.selected }
    output := state.next }

def selectiveConst {n : ℕ}
    (state : SelectiveState n) (value : Bool) : SelectiveWire n :=
  state.emit (.const value)

def selectiveInput {n : ℕ}
    (state : SelectiveState n) (index : Fin n) : SelectiveWire n :=
  state.emit (.input index)

def selectiveNot {n : ℕ}
    (state : SelectiveState n) (child : ℕ) : SelectiveWire n :=
  state.emit (.not child)

def selectiveAnd {n : ℕ}
    (state : SelectiveState n) (left right : ℕ) : SelectiveWire n :=
  state.emit (.and left right)

def selectiveOr {n : ℕ}
    (state : SelectiveState n) (left right : ℕ) : SelectiveWire n :=
  state.emit (.or left right)

def selectiveCompileExpr {n : ℕ} :
    SelectiveState n → BoolExpr n → SelectiveWire n
  | state, .const value => selectiveConst state value
  | state, .input index => selectiveInput state index
  | state, .not child =>
      let compiled := selectiveCompileExpr state child
      selectiveNot compiled.state compiled.output
  | state, .and left right =>
      let compiledLeft := selectiveCompileExpr state left
      let compiledRight :=
        selectiveCompileExpr compiledLeft.state right
      selectiveAnd compiledRight.state
        compiledLeft.output compiledRight.output
  | state, .or left right =>
      let compiledLeft := selectiveCompileExpr state left
      let compiledRight :=
        selectiveCompileExpr compiledLeft.state right
      selectiveOr compiledRight.state
        compiledLeft.output compiledRight.output

def selectiveCompileGuardedAny {n : ℕ} :
    SelectiveState n → List (BoolExpr n × ℕ) → SelectiveWire n
  | state, [] => selectiveConst state false
  | state, choice :: rest =>
      let condition := selectiveCompileExpr state choice.1
      let guarded :=
        selectiveAnd condition.state condition.output choice.2
      let tail := selectiveCompileGuardedAny guarded.state rest
      selectiveOr tail.state guarded.output tail.output
termination_by _state choices => choices.length

def selectiveCompileFieldSelect {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileGuardedAny state <|
    values.zipIdx.map fun entry =>
      (fieldEquals row entry.2, entry.1)

def selectiveCompileFirstFieldSelect {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileFieldSelect state firstFieldEqualsExpr row values

def selectiveCompileSecondFieldSelect {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileFieldSelect state secondFieldEqualsExpr row values

def selectiveCompileUniversalNode {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n)
    (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  let left :=
    selectiveCompileFirstFieldSelect state row priorValues
  let right :=
    selectiveCompileSecondFieldSelect left.state row priorValues
  let constantValue :=
    selectiveCompileExpr right.state (firstFieldEqualsExpr row 1)
  let inputValue :=
    selectiveCompileExpr constantValue.state
      (constantAddressSelectionExpr row address)
  let negated := selectiveNot inputValue.state left.output
  let conjunction :=
    selectiveAnd negated.state left.output right.output
  let disjunction :=
    selectiveOr conjunction.state left.output right.output
  selectiveCompileGuardedAny disjunction.state
    [ (tagEqualsExpr row 0, constantValue.output)
    , (tagEqualsExpr row 1, inputValue.output)
    , (tagEqualsExpr row 2, negated.output)
    , (tagEqualsExpr row 3, conjunction.output)
    , (tagEqualsExpr row 4, disjunction.output)
    ]

def selectiveCompileUniversalNodes {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (address : BitInput n) :
    (count : ℕ) → count ≤ bound →
      SelectiveWireList (descriptionWidth n bound)
  | 0, _ =>
      { state
        values := [] }
  | count + 1, hcount =>
      let earlier :=
        selectiveCompileUniversalNodes state address count (by omega)
      let row : Fin (bound + 1) := ⟨count, by omega⟩
      let node :=
        selectiveCompileUniversalNode earlier.state row address
          earlier.values
      { state := node.state
        values := earlier.values ++ [node.output] }

def selectiveCompileUniversalOutput {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    SelectiveWire (descriptionWidth n bound) :=
  let nodes :=
    selectiveCompileUniversalNodes state address count hcount
  let outputRow : Fin (bound + 1) := ⟨count, by omega⟩
  selectiveCompileFirstFieldSelect nodes.state outputRow nodes.values

def selectiveCompileUniversalOutputs {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound) :
    List (BitInput n) →
      SelectiveWireList (descriptionWidth n bound)
  | [] =>
      { state
        values := [] }
  | address :: rest =>
      let head :=
        selectiveCompileUniversalOutput state address count hcount
      let tail :=
        selectiveCompileUniversalOutputs head.state count hcount rest
      { state := tail.state
        values := head.output :: tail.values }

def selectiveLiteralWire {q : ℕ}
    (values : List ℕ) (literal : Literal q) : ℕ :=
  values.getD
    (match literal with
      | .positive query => query.val
      | .negative query => query.val)
    0

def selectiveCompileLiteral {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ) :
    Literal q → SelectiveWire n
  | .positive query =>
      { state
        output := values.getD query.val 0 }
  | .negative query =>
      selectiveNot state (values.getD query.val 0)

def selectiveCompileClause {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (clause : Fin 3 → Literal q) : SelectiveWire n :=
  let first := selectiveCompileLiteral state values (clause 0)
  let second := selectiveCompileLiteral first.state values (clause 1)
  let firstOrSecond :=
    selectiveOr second.state first.output second.output
  let third :=
    selectiveCompileLiteral firstOrSecond.state values (clause 2)
  selectiveOr third.state firstOrSecond.output third.output

def selectiveCompileClauses {q n : ℕ} :
    SelectiveState n → List ℕ → List (Fin 3 → Literal q) →
      SelectiveWire n
  | state, _values, [] => selectiveConst state true
  | state, values, clause :: rest =>
      let head := selectiveCompileClause state values clause
      let tail := selectiveCompileClauses head.state values rest
      selectiveAnd tail.state head.output tail.output

def selectiveCompileTableVerifierRow
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCode : ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  let addresses :=
    List.ofFn fun query : Fin count =>
      projectionTableAddress outputs width query.val
        (tableRandomness width randomnessCode)
  let queries :=
    selectiveCompileUniversalOutputs state nodeCount hnodeCount
      addresses
  selectiveCompileClauses queries.state queries.values <|
    (projectionTableDecision outputs width count randomnessCode).clauses

def selectiveCompileTableVerifierRows
    (outputs : List ℕ) (width count bound : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    SelectiveState (descriptionWidth width bound) → List ℕ →
      SelectiveWire (descriptionWidth width bound)
  | state, [] => selectiveConst state true
  | state, randomnessCode :: rest =>
      let head :=
        selectiveCompileTableVerifierRow outputs width count bound
          state nodeCount hnodeCount randomnessCode
      let tail :=
        selectiveCompileTableVerifierRows outputs width count bound
          nodeCount hnodeCount head.state rest
      selectiveAnd tail.state head.output tail.output

def selectiveCompileTableFixedCount
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) :
    SelectiveWire (descriptionWidth width bound) :=
  let grammar :=
    selectiveCompileExpr state
      (fixedCountGrammarExpr (n := width) candidate)
  let rows :=
    selectiveCompileTableVerifierRows outputs width count bound
      (candidate.val + 1) (by omega) grammar.state
      (List.range (2 ^ width))
  selectiveAnd rows.state grammar.output rows.output

def selectiveCompileTableCountCases
    (outputs : List ℕ) (width count bound : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      SelectiveWire (descriptionWidth width bound)
  | state, [] => selectiveConst state false
  | state, candidate :: rest =>
      let head :=
        selectiveCompileTableFixedCount outputs width count bound
          state candidate
      let tail :=
        selectiveCompileTableCountCases outputs width count bound
          head.state rest
      selectiveOr tail.state head.output tail.output

def selectiveCompileTableBoundedOracleVerifier
    (outputs : List ℕ) (width count bound target : ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileTableCountCases outputs width count bound
    (SelectiveState.empty (descriptionWidth width bound) target)
    (List.ofFn id)

/-- Exact pointwise response shape expected from the eventual fixed machine:
formula length and atom share one compiler pass. -/
def selectiveStructuralFormulaResponse
    (outputs : List ℕ) (width count bound index : ℕ) : ℕ × ℕ :=
  let inputArity := descriptionWidth width bound
  let target := index - inputArity
  let compiled :=
    selectiveCompileTableBoundedOracleVerifier
      outputs width count bound target
  let length := inputArity + compiled.state.next + 1
  let atom :=
    if _hinput : index < inputArity then
      circuitInputFormulaClauseTautologyAtom inputArity index
    else
      match compiled.state.selected with
      | some node =>
          circuitInputFormulaClauseNodeAtom target node
      | none =>
          circuitInputFormulaClauseNodeAtom compiled.output
            (.const true : BooleanNode inputArity)
  (length, atom)

/-! ## Refinement to the sole append-only builder -/

def SelectiveState.Matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n) : Prop :=
  state.next = builder.nodes.length ∧
    state.selected = builder.nodes[state.target]?

def SelectiveWire.Matches {n : ℕ}
    (wire : SelectiveWire n)
    {builder : BooleanDAGBuilder n} {function : BoolFunction n}
    (compiled : CompiledWire builder function) : Prop :=
  wire.state.Matches compiled.final ∧
    wire.output = compiled.output.val

def SelectiveWire.MatchesBuilt {n : ℕ}
    (wire : SelectiveWire n)
    {builder : BooleanDAGBuilder n}
    (compiled : BuiltWire builder) : Prop :=
  wire.state.Matches compiled.compiled.final ∧
    wire.output = compiled.compiled.output.val

def SelectiveWireList.Matches {n : ℕ}
    (raw : SelectiveWireList n)
    (final : BooleanDAGBuilder n)
    (values : List (LiveWire final)) : Prop :=
  raw.state.Matches final ∧
    raw.values = values.map fun value => value.output.val

@[simp] theorem SelectiveState.empty_matches (n target : ℕ) :
    (SelectiveState.empty n target).Matches
      (BooleanDAGBuilder.empty n) := by
  simp [SelectiveState.Matches, SelectiveState.empty,
    BooleanDAGBuilder.empty]

private theorem getElem?_append_singleton
    {α : Type} (values : List α) (value : α) (index : ℕ) :
    (values ++ [value])[index]? =
      if index = values.length then some value else values[index]? := by
  by_cases hlt : index < values.length
  · rw [List.getElem?_append_left hlt]
    rw [if_neg (by omega)]
  · by_cases heq : index = values.length
    · subst index
      simp
    · have hgt : values.length < index := by omega
      rw [List.getElem?_eq_none (by simp; omega)]
      rw [List.getElem?_eq_none (by omega)]
      simp [heq]

theorem SelectiveState.emit_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (hmatches : state.Matches builder) :
    (state.emit node).state.Matches
      (builder.appendNode node hnode) := by
  rcases hmatches with ⟨hnext, hselected⟩
  constructor
  · simp [SelectiveState.emit, hnext]
  · simp only [SelectiveState.emit,
      BooleanDAGBuilder.appendNode_nodes]
    rw [getElem?_append_singleton]
    rw [← hnext, hselected]

theorem selectiveConst_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (value : Bool) (hmatches : state.Matches builder) :
    (selectiveConst state value).Matches
      (compileConst builder value) := by
  constructor
  · exact state.emit_matches builder (.const value) trivial hmatches
  · simpa [selectiveConst, SelectiveState.emit, compileConst,
      BooleanDAGBuilder.newest] using hmatches.1

theorem selectiveInput_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (index : Fin n) (hmatches : state.Matches builder) :
    (selectiveInput state index).Matches
      (compileInput builder index) := by
  constructor
  · exact state.emit_matches builder (.input index) trivial hmatches
  · simpa [selectiveInput, SelectiveState.emit, compileInput,
      BooleanDAGBuilder.newest] using hmatches.1

theorem selectiveNot_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (child : ℕ) (wire : LiveWire builder)
    (hmatches : state.Matches builder)
    (hchild : child = wire.output.val) :
    (selectiveNot state child).Matches
      (compileNot builder wire) := by
  subst child
  constructor
  · exact state.emit_matches builder (.not wire.output.val)
      wire.output.isLt hmatches
  · simpa [selectiveNot, SelectiveState.emit, compileNot,
      LiveWire.stationary, CompiledWire.not,
      BooleanDAGBuilder.newest] using hmatches.1

theorem selectiveAnd_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (left right : ℕ) (leftWire rightWire : LiveWire builder)
    (hmatches : state.Matches builder)
    (hleft : left = leftWire.output.val)
    (hright : right = rightWire.output.val) :
    (selectiveAnd state left right).Matches
      (compileAnd builder leftWire rightWire) := by
  subst left
  subst right
  constructor
  · exact state.emit_matches builder
      (.and leftWire.output.val rightWire.output.val)
      ⟨leftWire.output.isLt, rightWire.output.isLt⟩ hmatches
  · simpa [selectiveAnd, SelectiveState.emit, compileAnd,
      LiveWire.stationary, CompiledWire.andThen, combineSequential,
      BooleanDAGBuilder.newest] using hmatches.1

theorem selectiveOr_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (left right : ℕ) (leftWire rightWire : LiveWire builder)
    (hmatches : state.Matches builder)
    (hleft : left = leftWire.output.val)
    (hright : right = rightWire.output.val) :
    (selectiveOr state left right).Matches
      (compileOr builder leftWire rightWire) := by
  subst left
  subst right
  constructor
  · exact state.emit_matches builder
      (.or leftWire.output.val rightWire.output.val)
      ⟨leftWire.output.isLt, rightWire.output.isLt⟩ hmatches
  · simpa [selectiveOr, SelectiveState.emit, compileOr,
      LiveWire.stationary, CompiledWire.orThen, combineSequential,
      BooleanDAGBuilder.newest] using hmatches.1

@[simp] private theorem compiledWire_live_output {n : ℕ}
    {prior : BooleanDAGBuilder n} {function : BoolFunction n}
    (wire : CompiledWire prior function) :
    wire.live.output = wire.output :=
  rfl

@[simp] private theorem liveWire_lift_output_val {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (wire : LiveWire prior) :
    (wire.lift extension).output.val = wire.output.val :=
  rfl

theorem selectiveCompileExpr_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (expression : BoolExpr n) (hmatches : state.Matches builder) :
    (selectiveCompileExpr state expression).Matches
      (compileExpr builder expression) := by
  induction expression generalizing state builder with
  | const value =>
      exact selectiveConst_matches state builder value hmatches
  | input index =>
      exact selectiveInput_matches state builder index hmatches
  | not child inductionHypothesis =>
      let raw := selectiveCompileExpr state child
      let compiled := compileExpr builder child
      have hchild : raw.Matches compiled :=
        inductionHypothesis state builder hmatches
      have hnot :=
        selectiveNot_matches raw.state compiled.final raw.output
          compiled.live hchild.1 hchild.2
      constructor
      · simpa [selectiveCompileExpr, compileExpr, raw, compiled,
          compileNot, LiveWire.stationary, CompiledWire.not] using
          hnot.1
      · simpa [selectiveCompileExpr, compileExpr, raw, compiled,
          compileNot, LiveWire.stationary, CompiledWire.not] using
          hnot.2
  | and left right leftHypothesis rightHypothesis =>
      let rawLeft := selectiveCompileExpr state left
      let compiledLeft := compileExpr builder left
      have hleft : rawLeft.Matches compiledLeft :=
        leftHypothesis state builder hmatches
      let rawRight := selectiveCompileExpr rawLeft.state right
      let compiledRight :=
        compileExpr compiledLeft.final right
      have hright : rawRight.Matches compiledRight :=
        rightHypothesis rawLeft.state compiledLeft.final hleft.1
      let liftedLeft :=
        compiledLeft.live.lift compiledRight.extension
      have hcombined :=
        selectiveAnd_matches rawRight.state compiledRight.final
          rawLeft.output rawRight.output liftedLeft
          compiledRight.live hright.1
          (by
            simpa [liftedLeft, LiveWire.lift] using hleft.2)
          hright.2
      constructor
      · simpa [selectiveCompileExpr, compileExpr, rawLeft,
          compiledLeft, rawRight, compiledRight, liftedLeft,
          compileAnd, LiveWire.stationary, CompiledWire.andThen,
          combineSequential] using hcombined.1
      · simpa [selectiveCompileExpr, compileExpr, rawLeft,
          compiledLeft, rawRight, compiledRight, liftedLeft,
          compileAnd, LiveWire.stationary, CompiledWire.andThen,
          combineSequential] using hcombined.2
  | or left right leftHypothesis rightHypothesis =>
      let rawLeft := selectiveCompileExpr state left
      let compiledLeft := compileExpr builder left
      have hleft : rawLeft.Matches compiledLeft :=
        leftHypothesis state builder hmatches
      let rawRight := selectiveCompileExpr rawLeft.state right
      let compiledRight :=
        compileExpr compiledLeft.final right
      have hright : rawRight.Matches compiledRight :=
        rightHypothesis rawLeft.state compiledLeft.final hleft.1
      let liftedLeft :=
        compiledLeft.live.lift compiledRight.extension
      have hcombined :=
        selectiveOr_matches rawRight.state compiledRight.final
          rawLeft.output rawRight.output liftedLeft
          compiledRight.live hright.1
          (by
            simpa [liftedLeft, LiveWire.lift] using hleft.2)
          hright.2
      constructor
      · simpa [selectiveCompileExpr, compileExpr, rawLeft,
          compiledLeft, rawRight, compiledRight, liftedLeft,
          compileOr, LiveWire.stationary, CompiledWire.orThen,
          combineSequential] using hcombined.1
      · simpa [selectiveCompileExpr, compileExpr, rawLeft,
          compiledLeft, rawRight, compiledRight, liftedLeft,
          compileOr, LiveWire.stationary, CompiledWire.orThen,
          combineSequential] using hcombined.2

theorem selectiveCompileGuardedAny_matches {n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (choices : List (GuardedChoice builder))
    (hmatches : state.Matches builder) :
    (selectiveCompileGuardedAny state <|
        choices.map fun choice =>
          (choice.condition, choice.value.output.val)).Matches
      (compileGuardedAny builder choices) := by
  cases choices with
  | nil =>
      simpa [selectiveCompileGuardedAny, compileGuardedAny] using
        selectiveConst_matches state builder false hmatches
  | cons choice rest =>
      let rawCondition :=
        selectiveCompileExpr state choice.condition
      let condition :=
        compileExpr builder choice.condition
      have hcondition : rawCondition.Matches condition :=
        selectiveCompileExpr_matches state builder choice.condition hmatches
      let rawGuarded :=
        selectiveAnd rawCondition.state rawCondition.output
          choice.value.output.val
      let guarded :=
        compileAnd condition.final condition.live
          (choice.value.lift condition.extension)
      have hguarded : rawGuarded.Matches guarded :=
        selectiveAnd_matches rawCondition.state condition.final
          rawCondition.output choice.value.output.val
          condition.live (choice.value.lift condition.extension)
          hcondition.1 hcondition.2 (by rfl)
      let headExtension :=
        condition.extension.trans guarded.extension
      let liftedRest :=
        rest.map (GuardedChoice.lift headExtension)
      let rawTail :=
        selectiveCompileGuardedAny rawGuarded.state <|
          rest.map fun original =>
            (original.condition, original.value.output.val)
      let tail :=
        compileGuardedAny guarded.final liftedRest
      have htail : rawTail.Matches tail := by
        have hlifted :
            liftedRest.map (fun lifted =>
                (lifted.condition, lifted.value.output.val)) =
              rest.map (fun original =>
                (original.condition, original.value.output.val)) := by
          simp [liftedRest, GuardedChoice.lift, LiveWire.lift]
        have hinduction :=
          selectiveCompileGuardedAny_matches rawGuarded.state
            guarded.final liftedRest hguarded.1
        simpa [rawTail, tail, hlifted] using hinduction
      let rawMerged :=
        selectiveOr rawTail.state rawGuarded.output rawTail.output
      let merged :=
        compileOr tail.final
          (guarded.live.lift tail.extension) tail.live
      have hmerged : rawMerged.Matches merged :=
        selectiveOr_matches rawTail.state tail.final
          rawGuarded.output rawTail.output
          (guarded.live.lift tail.extension) tail.live
          htail.1 (by
            simpa [LiveWire.lift] using hguarded.2) htail.2
      constructor
      · simpa [selectiveCompileGuardedAny, compileGuardedAny,
          rawCondition, condition, rawGuarded, guarded,
          headExtension, liftedRest, rawTail, tail, rawMerged, merged,
          CompiledWire.prepend] using hmerged.1
      · have hrawOutput :
            (selectiveCompileGuardedAny state <|
                (choice :: rest).map fun current =>
                  (current.condition, current.value.output.val)).output =
              rawMerged.output := by
            simp only [List.map_cons, selectiveCompileGuardedAny]
            rfl
        have hcompiledOutput :
            (compileGuardedAny builder (choice :: rest)).output.val =
              merged.output.val := by
            rw [compileGuardedAny]
            rfl
        calc
          _ = rawMerged.output := hrawOutput
          _ = merged.output.val := hmerged.2
          _ = _ := hcompiledOutput.symm
termination_by choices.length
decreasing_by simp

theorem selectiveCompileFieldSelect_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileFieldSelect state fieldEquals row rawValues).Matches
      (compileFieldSelect builder fieldEquals row values) := by
  have hguarded :=
    selectiveCompileGuardedAny_matches state builder
      (fieldChoices fieldEquals row values) hmatches
  constructor
  · simpa [selectiveCompileFieldSelect, compileFieldSelect, fieldChoices,
      hvalues, List.zipIdx_map, Function.comp_def] using hguarded.1
  · simpa [selectiveCompileFieldSelect, compileFieldSelect, fieldChoices,
      hvalues, List.zipIdx_map, Function.comp_def] using hguarded.2

theorem selectiveCompileFirstFieldSelect_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileFirstFieldSelect state row rawValues).Matches
      (compileFirstFieldSelect builder row values) := by
  exact selectiveCompileFieldSelect_matches state builder
    firstFieldEqualsExpr row rawValues values hmatches hvalues

theorem selectiveCompileSecondFieldSelect_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileSecondFieldSelect state row rawValues).Matches
      (compileSecondFieldSelect builder row values) := by
  exact selectiveCompileFieldSelect_matches state builder
    secondFieldEqualsExpr row rawValues values hmatches hvalues

theorem selectiveCompileUniversalNode_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n)
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileUniversalNode state row address rawValues).MatchesBuilt
      (compileUniversalNode builder row address values) := by
  let rawLeft :=
    selectiveCompileFirstFieldSelect state row rawValues
  let left :=
    compileFirstFieldSelect builder row values
  have hleft : rawLeft.Matches left :=
    selectiveCompileFirstFieldSelect_matches state builder row
      rawValues values hmatches hvalues
  let valuesAtLeft := liftLiveWires left.extension values
  let rawRight :=
    selectiveCompileSecondFieldSelect rawLeft.state row rawValues
  let right :=
    compileSecondFieldSelect left.final row valuesAtLeft
  have hvaluesAtLeft :
      rawValues =
        valuesAtLeft.map fun value => value.output.val := by
    rw [hvalues]
    simp [valuesAtLeft, liftLiveWires, LiveWire.lift,
      Function.comp_def]
  have hright : rawRight.Matches right :=
    selectiveCompileSecondFieldSelect_matches rawLeft.state left.final row
      rawValues valuesAtLeft hleft.1 hvaluesAtLeft
  let leftAtRight := left.live.lift right.extension
  let rawConstant :=
    selectiveCompileExpr rawRight.state (firstFieldEqualsExpr row 1)
  let constantValue :=
    compileExpr right.final (firstFieldEqualsExpr row 1)
  have hconstant : rawConstant.Matches constantValue :=
    selectiveCompileExpr_matches rawRight.state right.final
      (firstFieldEqualsExpr row 1) hright.1
  let leftAtConstant := leftAtRight.lift constantValue.extension
  let rightAtConstant := right.live.lift constantValue.extension
  let rawInput :=
    selectiveCompileExpr rawConstant.state
      (constantAddressSelectionExpr row address)
  let inputValue :=
    compileExpr constantValue.final
      (constantAddressSelectionExpr row address)
  have hinput : rawInput.Matches inputValue :=
    selectiveCompileExpr_matches rawConstant.state constantValue.final
      (constantAddressSelectionExpr row address) hconstant.1
  let leftAtInput := leftAtConstant.lift inputValue.extension
  let rightAtInput := rightAtConstant.lift inputValue.extension
  let rawNegated :=
    selectiveNot rawInput.state rawLeft.output
  let negated :=
    compileNot inputValue.final leftAtInput
  have hnegated : rawNegated.Matches negated :=
    selectiveNot_matches rawInput.state inputValue.final rawLeft.output
      leftAtInput hinput.1 (by
        simpa [leftAtInput, leftAtConstant, leftAtRight,
          LiveWire.lift] using hleft.2)
  let leftAtNegated := leftAtInput.lift negated.extension
  let rightAtNegated := rightAtInput.lift negated.extension
  let rawConjunction :=
    selectiveAnd rawNegated.state rawLeft.output rawRight.output
  let conjunction :=
    compileAnd negated.final leftAtNegated rightAtNegated
  have hconjunction : rawConjunction.Matches conjunction :=
    selectiveAnd_matches rawNegated.state negated.final
      rawLeft.output rawRight.output leftAtNegated rightAtNegated
      hnegated.1
      (by
        simpa [leftAtNegated, leftAtInput, leftAtConstant,
          leftAtRight, LiveWire.lift] using hleft.2)
      (by
        simpa [rightAtNegated, rightAtInput, rightAtConstant,
          LiveWire.lift] using hright.2)
  let leftAtConjunction :=
    leftAtNegated.lift conjunction.extension
  let rightAtConjunction :=
    rightAtNegated.lift conjunction.extension
  let rawDisjunction :=
    selectiveOr rawConjunction.state rawLeft.output rawRight.output
  let disjunction :=
    compileOr conjunction.final leftAtConjunction rightAtConjunction
  have hdisjunction : rawDisjunction.Matches disjunction :=
    selectiveOr_matches rawConjunction.state conjunction.final
      rawLeft.output rawRight.output leftAtConjunction
      rightAtConjunction hconjunction.1
      (by
        simpa [leftAtConjunction, leftAtNegated, leftAtInput,
          leftAtConstant, leftAtRight, LiveWire.lift] using hleft.2)
      (by
        simpa [rightAtConjunction, rightAtNegated, rightAtInput,
          rightAtConstant, LiveWire.lift] using hright.2)
  let caseExtension :=
    left.extension.trans <| right.extension.trans <|
      constantValue.extension.trans <| inputValue.extension.trans <|
        negated.extension.trans <|
          conjunction.extension.trans disjunction.extension
  let choices : List (GuardedChoice disjunction.final) :=
    [ { condition := tagEqualsExpr row 0
        value :=
          constantValue.live.lift <|
            inputValue.extension.trans <| negated.extension.trans <|
              conjunction.extension.trans disjunction.extension }
    , { condition := tagEqualsExpr row 1
        value :=
          inputValue.live.lift <| negated.extension.trans <|
            conjunction.extension.trans disjunction.extension }
    , { condition := tagEqualsExpr row 2
        value :=
          negated.live.lift <|
            conjunction.extension.trans disjunction.extension }
    , { condition := tagEqualsExpr row 3
        value := conjunction.live.lift disjunction.extension }
    , { condition := tagEqualsExpr row 4
        value := disjunction.live }
    ]
  let rawSelected :=
    selectiveCompileGuardedAny rawDisjunction.state
      [ (tagEqualsExpr row 0, rawConstant.output)
      , (tagEqualsExpr row 1, rawInput.output)
      , (tagEqualsExpr row 2, rawNegated.output)
      , (tagEqualsExpr row 3, rawConjunction.output)
      , (tagEqualsExpr row 4, rawDisjunction.output)
      ]
  let selected :=
    compileGuardedAny disjunction.final choices
  have hselected : rawSelected.Matches selected := by
    have hchoices :=
      selectiveCompileGuardedAny_matches rawDisjunction.state
        disjunction.final choices hdisjunction.1
    constructor
    · simpa [rawSelected, choices, selected, LiveWire.lift,
        rawConstant, rawInput, rawNegated, rawConjunction,
        rawDisjunction, compiledWire_live_output,
        hconstant.2, hinput.2, hnegated.2, hconjunction.2,
        hdisjunction.2] using hchoices.1
    · simpa [rawSelected, choices, selected, LiveWire.lift,
        rawConstant, rawInput, rawNegated, rawConjunction,
        rawDisjunction, compiledWire_live_output,
        hconstant.2, hinput.2, hnegated.2, hconjunction.2,
        hdisjunction.2] using hchoices.2
  constructor
  · simpa [selectiveCompileUniversalNode, compileUniversalNode,
      rawLeft, left, valuesAtLeft, rawRight, right, leftAtRight,
      rawConstant, constantValue, leftAtConstant, rightAtConstant,
      rawInput, inputValue, leftAtInput, rightAtInput, rawNegated,
      negated, leftAtNegated, rightAtNegated, rawConjunction,
      conjunction, leftAtConjunction, rightAtConjunction,
      rawDisjunction, disjunction, caseExtension, choices,
      rawSelected, selected, CompiledWire.prepend] using hselected.1
  · simpa [selectiveCompileUniversalNode, compileUniversalNode,
      rawLeft, left, valuesAtLeft, rawRight, right, leftAtRight,
      rawConstant, constantValue, leftAtConstant, rightAtConstant,
      rawInput, inputValue, leftAtInput, rightAtInput, rawNegated,
      negated, leftAtNegated, rightAtNegated, rawConjunction,
      conjunction, leftAtConjunction, rightAtConjunction,
      rawDisjunction, disjunction, caseExtension, choices,
      rawSelected, selected, CompiledWire.prepend] using hselected.2

theorem selectiveCompileUniversalNodes_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (hmatches : state.Matches builder) :
    (selectiveCompileUniversalNodes state address count hcount).Matches
      (compileUniversalNodes builder address count hcount).final
      (compileUniversalNodes builder address count hcount).values := by
  induction count generalizing state builder with
  | zero =>
      exact ⟨hmatches, rfl⟩
  | succ count inductionHypothesis =>
      let rawEarlier :=
        selectiveCompileUniversalNodes state address count (by omega)
      let earlier :=
        compileUniversalNodes builder address count (by omega)
      have hearlier : rawEarlier.Matches earlier.final earlier.values :=
        inductionHypothesis state builder (by omega) hmatches
      let row : Fin (bound + 1) := ⟨count, by omega⟩
      let rawNode :=
        selectiveCompileUniversalNode rawEarlier.state row address
          rawEarlier.values
      let node :=
        compileUniversalNode earlier.final row address earlier.values
      have hnode : rawNode.MatchesBuilt node :=
        selectiveCompileUniversalNode_matches rawEarlier.state
          earlier.final row address rawEarlier.values earlier.values
          hearlier.1 hearlier.2
      constructor
      · simpa [selectiveCompileUniversalNodes,
          compileUniversalNodes, rawEarlier, earlier, row, rawNode, node]
          using hnode.1
      · change
          rawEarlier.values ++ [rawNode.output] =
            (liftLiveWires node.compiled.extension earlier.values ++
              [node.live]).map fun value => value.output.val
        rw [hearlier.2, hnode.2]
        simp [liftLiveWires, LiveWire.lift, BuiltWire.live,
          Function.comp_def]

theorem selectiveCompileUniversalOutput_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (hmatches : state.Matches builder) :
    (selectiveCompileUniversalOutput state address count hcount).MatchesBuilt
      (compileUniversalOutput builder address count hcount) := by
  let rawNodes :=
    selectiveCompileUniversalNodes state address count hcount
  let nodes :=
    compileUniversalNodes builder address count hcount
  have hnodes : rawNodes.Matches nodes.final nodes.values :=
    selectiveCompileUniversalNodes_matches state builder address count
      hcount hmatches
  let outputRow : Fin (bound + 1) := ⟨count, by omega⟩
  let rawSelected :=
    selectiveCompileFirstFieldSelect rawNodes.state outputRow
      rawNodes.values
  let selected :=
    compileFirstFieldSelect nodes.final outputRow nodes.values
  have hselected : rawSelected.Matches selected :=
    selectiveCompileFirstFieldSelect_matches rawNodes.state nodes.final
      outputRow rawNodes.values nodes.values hnodes.1 hnodes.2
  constructor
  · simpa [selectiveCompileUniversalOutput, compileUniversalOutput,
      rawNodes, nodes, outputRow, rawSelected, selected,
      CompiledWire.prepend] using hselected.1
  · simpa [selectiveCompileUniversalOutput, compileUniversalOutput,
      rawNodes, nodes, outputRow, rawSelected, selected,
      CompiledWire.prepend] using hselected.2

theorem selectiveCompileUniversalOutputs_matches {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound)
    (addresses : List (BitInput n))
    (hmatches : state.Matches builder) :
    (selectiveCompileUniversalOutputs state count hcount addresses).Matches
      (compileUniversalOutputs builder count hcount addresses).final
      (compileUniversalOutputs builder count hcount addresses).values := by
  induction addresses generalizing state builder with
  | nil =>
      exact ⟨hmatches, rfl⟩
  | cons address rest inductionHypothesis =>
      let rawHead :=
        selectiveCompileUniversalOutput state address count hcount
      let head :=
        compileUniversalOutput builder address count hcount
      have hhead : rawHead.MatchesBuilt head :=
        selectiveCompileUniversalOutput_matches state builder address
          count hcount hmatches
      let rawTail :=
        selectiveCompileUniversalOutputs rawHead.state count hcount rest
      let tail :=
        compileUniversalOutputs head.compiled.final count hcount rest
      have htail : rawTail.Matches tail.final tail.values :=
        inductionHypothesis rawHead.state head.compiled.final hhead.1
      constructor
      · simpa [selectiveCompileUniversalOutputs,
          compileUniversalOutputs, rawHead, head, rawTail, tail]
          using htail.1
      · change
          rawHead.output :: rawTail.values =
            (head.live.lift tail.extension :: tail.values).map
              fun value => value.output.val
        rw [hhead.2, htail.2]
        simp [LiveWire.lift, BuiltWire.live]

theorem selectiveLiteralWire_eq {q n : ℕ}
    (rawValues : List ℕ) {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (hvalues :
      rawValues = values.map fun value => value.output.val)
    (literal : Literal q) :
    selectiveLiteralWire rawValues literal =
      (literalWire values hlength literal).output.val := by
  cases literal with
  | positive query =>
      have hbound : query.val < rawValues.length := by
        rw [hvalues, List.length_map, hlength]
        exact query.isLt
      rw [selectiveLiteralWire, List.getD_eq_getElem _ _ hbound]
      simp [literalWire, hvalues]
  | negative query =>
      have hbound : query.val < rawValues.length := by
        rw [hvalues, List.length_map, hlength]
        exact query.isLt
      rw [selectiveLiteralWire, List.getD_eq_getElem _ _ hbound]
      simp [literalWire, hvalues]

theorem selectiveCompileLiteral_matches {q n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hlength : values.length = q)
    (literal : Literal q) (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileLiteral state rawValues literal).MatchesBuilt
      (compileLiteral builder values hlength literal) := by
  cases literal with
  | positive query =>
      constructor
      · exact hmatches
      · exact selectiveLiteralWire_eq rawValues values hlength hvalues
          (.positive query)
  | negative query =>
      have hnot :=
        selectiveNot_matches state builder
          (rawValues.getD query.val 0)
          (literalWire values hlength (.negative query))
          hmatches
          (selectiveLiteralWire_eq rawValues values hlength hvalues
            (.negative query))
      exact hnot

theorem selectiveCompileClause_matches {q n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hlength : values.length = q)
    (clause : Fin 3 → Literal q)
    (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileClause state rawValues clause).MatchesBuilt
      (compileClause builder values hlength clause) := by
  let rawFirst :=
    selectiveCompileLiteral state rawValues (clause 0)
  let first :=
    compileLiteral builder values hlength (clause 0)
  have hfirst : rawFirst.MatchesBuilt first :=
    selectiveCompileLiteral_matches state builder rawValues values
      hlength (clause 0) hmatches hvalues
  let valuesAtFirst :=
    liftLiveWires first.compiled.extension values
  let valuesAtFirstLength : valuesAtFirst.length = q := by
    dsimp only [valuesAtFirst]
    rw [liftLiveWires_length]
    exact hlength
  have hvaluesAtFirst :
      rawValues =
        valuesAtFirst.map fun value => value.output.val := by
    rw [hvalues]
    simp [valuesAtFirst, liftLiveWires, LiveWire.lift,
      Function.comp_def]
  let rawSecond :=
    selectiveCompileLiteral rawFirst.state rawValues (clause 1)
  let second :=
    compileLiteral first.compiled.final valuesAtFirst
      valuesAtFirstLength (clause 1)
  have hsecond : rawSecond.MatchesBuilt second :=
    selectiveCompileLiteral_matches rawFirst.state first.compiled.final
      rawValues valuesAtFirst valuesAtFirstLength (clause 1)
      hfirst.1 hvaluesAtFirst
  let firstAtSecond :=
    first.live.lift second.compiled.extension
  let rawFirstOrSecond :=
    selectiveOr rawSecond.state rawFirst.output rawSecond.output
  let firstOrSecond :=
    compileOr second.compiled.final firstAtSecond second.live
  have hfirstOrSecond : rawFirstOrSecond.Matches firstOrSecond :=
    selectiveOr_matches rawSecond.state second.compiled.final
      rawFirst.output rawSecond.output firstAtSecond second.live
      hsecond.1
      (by
        simpa [firstAtSecond, LiveWire.lift, BuiltWire.live] using
          hfirst.2)
      hsecond.2
  let valuesAtDisjunction :=
    liftLiveWires
      (first.compiled.extension.trans <|
        second.compiled.extension.trans firstOrSecond.extension)
      values
  let valuesAtDisjunctionLength :
      valuesAtDisjunction.length = q := by
    dsimp only [valuesAtDisjunction]
    rw [liftLiveWires_length]
    exact hlength
  have hvaluesAtDisjunction :
      rawValues =
        valuesAtDisjunction.map fun value => value.output.val := by
    rw [hvalues]
    simp [valuesAtDisjunction, liftLiveWires, LiveWire.lift,
      Function.comp_def]
  let rawThird :=
    selectiveCompileLiteral rawFirstOrSecond.state rawValues (clause 2)
  let third :=
    compileLiteral firstOrSecond.final valuesAtDisjunction
      valuesAtDisjunctionLength (clause 2)
  have hthird : rawThird.MatchesBuilt third :=
    selectiveCompileLiteral_matches rawFirstOrSecond.state
      firstOrSecond.final rawValues valuesAtDisjunction
      valuesAtDisjunctionLength (clause 2) hfirstOrSecond.1
      hvaluesAtDisjunction
  let disjunctionAtThird :=
    firstOrSecond.live.lift third.compiled.extension
  let rawOutput :=
    selectiveOr rawThird.state rawFirstOrSecond.output rawThird.output
  let output :=
    compileOr third.compiled.final disjunctionAtThird third.live
  have houtput : rawOutput.Matches output :=
    selectiveOr_matches rawThird.state third.compiled.final
      rawFirstOrSecond.output rawThird.output disjunctionAtThird
      third.live hthird.1
      (by
        simpa [disjunctionAtThird, LiveWire.lift] using
          hfirstOrSecond.2)
      hthird.2
  constructor
  · simpa [selectiveCompileClause, compileClause, rawFirst, first,
      valuesAtFirst, valuesAtFirstLength, rawSecond, second,
      firstAtSecond, rawFirstOrSecond, firstOrSecond,
      valuesAtDisjunction, valuesAtDisjunctionLength, rawThird, third,
      disjunctionAtThird, rawOutput, output, CompiledWire.prepend]
      using houtput.1
  · simpa [selectiveCompileClause, compileClause, rawFirst, first,
      valuesAtFirst, valuesAtFirstLength, rawSecond, second,
      firstAtSecond, rawFirstOrSecond, firstOrSecond,
      valuesAtDisjunction, valuesAtDisjunctionLength, rawThird, third,
      disjunctionAtThird, rawOutput, output, CompiledWire.prepend]
      using houtput.2

theorem selectiveCompileClauses_matches {q n : ℕ}
    (state : SelectiveState n) (builder : BooleanDAGBuilder n)
    (rawValues : List ℕ) (values : List (LiveWire builder))
    (hlength : values.length = q)
    (clauses : List (Fin 3 → Literal q))
    (hmatches : state.Matches builder)
    (hvalues :
      rawValues = values.map fun value => value.output.val) :
    (selectiveCompileClauses state rawValues clauses).Matches
      (compileClauses builder values hlength clauses) := by
  induction clauses generalizing state builder rawValues values with
  | nil =>
      have hconstant :=
        selectiveConst_matches state builder true hmatches
      exact ⟨hconstant.1, hconstant.2⟩
  | cons clause rest inductionHypothesis =>
      let rawHead :=
        selectiveCompileClause state rawValues clause
      let head :=
        compileClause builder values hlength clause
      have hhead : rawHead.MatchesBuilt head :=
        selectiveCompileClause_matches state builder rawValues values
          hlength clause hmatches hvalues
      let valuesAtHead :=
        liftLiveWires head.compiled.extension values
      let valuesAtHeadLength : valuesAtHead.length = q := by
        dsimp only [valuesAtHead]
        rw [liftLiveWires_length]
        exact hlength
      have hvaluesAtHead :
          rawValues =
            valuesAtHead.map fun value => value.output.val := by
        rw [hvalues]
        simp [valuesAtHead, liftLiveWires, LiveWire.lift,
          Function.comp_def]
      let rawTail :=
        selectiveCompileClauses rawHead.state rawValues rest
      let tail :=
        compileClauses head.compiled.final valuesAtHead
          valuesAtHeadLength rest
      have htail : rawTail.Matches tail :=
        inductionHypothesis rawHead.state head.compiled.final rawValues
          valuesAtHead valuesAtHeadLength hhead.1 hvaluesAtHead
      let headAtTail :=
        head.live.lift tail.extension
      let rawConjunction :=
        selectiveAnd rawTail.state rawHead.output rawTail.output
      let conjunction :=
        compileAnd tail.final headAtTail tail.live
      have hconjunction : rawConjunction.Matches conjunction :=
        selectiveAnd_matches rawTail.state tail.final
          rawHead.output rawTail.output headAtTail tail.live htail.1
          (by
            simpa [headAtTail, LiveWire.lift, BuiltWire.live] using
              hhead.2)
          htail.2
      constructor
      · simpa [selectiveCompileClauses, compileClauses, rawHead, head,
          valuesAtHead, valuesAtHeadLength, rawTail, tail, headAtTail,
          rawConjunction, conjunction, CompiledWire.prepend] using
          hconjunction.1
      · simpa [selectiveCompileClauses, compileClauses, rawHead, head,
          valuesAtHead, valuesAtHeadLength, rawTail, tail, headAtTail,
          rawConjunction, conjunction, CompiledWire.prepend] using
          hconjunction.2

theorem selectiveCompileTableVerifierRow_matches
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCode : ℕ) (hmatches : state.Matches builder) :
    (selectiveCompileTableVerifierRow outputs width count bound state
        nodeCount hnodeCount randomnessCode).MatchesBuilt
      (compileTableVerifierRow outputs width count bound builder
        nodeCount hnodeCount randomnessCode) := by
  let addresses :=
    List.ofFn fun query : Fin count =>
      projectionTableAddress outputs width query.val
        (tableRandomness width randomnessCode)
  let rawQueries :=
    selectiveCompileUniversalOutputs state nodeCount hnodeCount
      addresses
  let queries :=
    compileUniversalOutputs builder nodeCount hnodeCount addresses
  have hqueries : rawQueries.Matches queries.final queries.values :=
    selectiveCompileUniversalOutputs_matches state builder nodeCount
      hnodeCount addresses hmatches
  let queryLength : queries.values.length = count := by
    rw [compileUniversalOutputs_values_length]
    simp [addresses]
  let rawDecision :=
    selectiveCompileClauses rawQueries.state rawQueries.values <|
      (projectionTableDecision outputs width count randomnessCode).clauses
  let decision :=
    compileClauses queries.final queries.values queryLength <|
      (projectionTableDecision outputs width count randomnessCode).clauses
  have hdecision : rawDecision.Matches decision :=
    selectiveCompileClauses_matches rawQueries.state queries.final
      rawQueries.values queries.values queryLength
      (projectionTableDecision outputs width count randomnessCode).clauses
      hqueries.1 hqueries.2
  constructor
  · simpa [selectiveCompileTableVerifierRow,
      compileTableVerifierRow, compileVerifierRowData, addresses,
      rawQueries, queries, queryLength, rawDecision, decision,
      CompiledWire.prepend] using hdecision.1
  · simpa [selectiveCompileTableVerifierRow,
      compileTableVerifierRow, compileVerifierRowData, addresses,
      rawQueries, queries, queryLength, rawDecision, decision,
      CompiledWire.prepend] using hdecision.2

theorem selectiveCompileTableVerifierRows_matches
    (outputs : List ℕ) (width count bound : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound))
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (randomnessCodes : List ℕ) (hmatches : state.Matches builder) :
    (selectiveCompileTableVerifierRows outputs width count bound
        nodeCount hnodeCount state randomnessCodes).MatchesBuilt
      (compileTableVerifierRows outputs width count bound
        nodeCount hnodeCount builder randomnessCodes) := by
  induction randomnessCodes generalizing state builder with
  | nil =>
      have hconstant :=
        selectiveConst_matches state builder true hmatches
      exact ⟨hconstant.1, hconstant.2⟩
  | cons randomnessCode rest inductionHypothesis =>
      let rawHead :=
        selectiveCompileTableVerifierRow outputs width count bound
          state nodeCount hnodeCount randomnessCode
      let head :=
        compileTableVerifierRow outputs width count bound builder
          nodeCount hnodeCount randomnessCode
      have hhead : rawHead.MatchesBuilt head :=
        selectiveCompileTableVerifierRow_matches outputs width count bound
          state builder nodeCount hnodeCount randomnessCode hmatches
      let rawTail :=
        selectiveCompileTableVerifierRows outputs width count bound
          nodeCount hnodeCount rawHead.state rest
      let tail :=
        compileTableVerifierRows outputs width count bound
          nodeCount hnodeCount head.compiled.final rest
      have htail : rawTail.MatchesBuilt tail :=
        inductionHypothesis rawHead.state head.compiled.final hhead.1
      let headAtTail :=
        head.live.lift tail.compiled.extension
      let rawConjunction :=
        selectiveAnd rawTail.state rawHead.output rawTail.output
      let conjunction :=
        compileAnd tail.compiled.final headAtTail tail.live
      have hconjunction : rawConjunction.Matches conjunction :=
        selectiveAnd_matches rawTail.state tail.compiled.final
          rawHead.output rawTail.output headAtTail tail.live htail.1
          (by
            simpa [headAtTail, LiveWire.lift, BuiltWire.live] using
              hhead.2)
          htail.2
      constructor
      · simpa [selectiveCompileTableVerifierRows,
          compileTableVerifierRows, rawHead, head, rawTail, tail,
          headAtTail, rawConjunction, conjunction,
          BuiltWire.ofCompiled, CompiledWire.prepend] using
          hconjunction.1
      · simpa [selectiveCompileTableVerifierRows,
          compileTableVerifierRows, rawHead, head, rawTail, tail,
          headAtTail, rawConjunction, conjunction,
          BuiltWire.ofCompiled, CompiledWire.prepend] using
          hconjunction.2

theorem selectiveCompileTableFixedCount_matches
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (candidate : Fin bound) (hmatches : state.Matches builder) :
    (selectiveCompileTableFixedCount outputs width count bound
        state candidate).MatchesBuilt
      (compileTableFixedCount outputs width count bound
        builder candidate) := by
  let rawGrammar :=
    selectiveCompileExpr state
      (fixedCountGrammarExpr (n := width) candidate)
  let grammar :=
    compileExpr builder
      (fixedCountGrammarExpr (n := width) candidate)
  have hgrammar : rawGrammar.Matches grammar :=
    selectiveCompileExpr_matches state builder
      (fixedCountGrammarExpr (n := width) candidate) hmatches
  let rawRows :=
    selectiveCompileTableVerifierRows outputs width count bound
      (candidate.val + 1) (by omega) rawGrammar.state
      (List.range (2 ^ width))
  let rows :=
    compileTableVerifierRows outputs width count bound
      (candidate.val + 1) (by omega) grammar.final
      (List.range (2 ^ width))
  have hrows : rawRows.MatchesBuilt rows :=
    selectiveCompileTableVerifierRows_matches outputs width count bound
      (candidate.val + 1) (by omega) rawGrammar.state grammar.final
      (List.range (2 ^ width)) hgrammar.1
  let grammarAtRows :=
    grammar.live.lift rows.compiled.extension
  let rawConjunction :=
    selectiveAnd rawRows.state rawGrammar.output rawRows.output
  let conjunction :=
    compileAnd rows.compiled.final grammarAtRows rows.live
  have hconjunction : rawConjunction.Matches conjunction :=
    selectiveAnd_matches rawRows.state rows.compiled.final
      rawGrammar.output rawRows.output grammarAtRows rows.live hrows.1
      (by
        simpa [grammarAtRows, LiveWire.lift] using hgrammar.2)
      hrows.2
  constructor
  · simpa [selectiveCompileTableFixedCount, compileTableFixedCount,
      compileFixedCountWithRows, rawGrammar, grammar, rawRows, rows,
      grammarAtRows, rawConjunction, conjunction,
      BuiltWire.ofCompiled, CompiledWire.prepend] using
      hconjunction.1
  · simpa [selectiveCompileTableFixedCount, compileTableFixedCount,
      compileFixedCountWithRows, rawGrammar, grammar, rawRows, rows,
      grammarAtRows, rawConjunction, conjunction,
      BuiltWire.ofCompiled, CompiledWire.prepend] using
      hconjunction.2

theorem selectiveCompileTableCountCases_matches
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (candidates : List (Fin bound))
    (hmatches : state.Matches builder) :
    (selectiveCompileTableCountCases outputs width count bound
        state candidates).MatchesBuilt
      (compileTableCountCases outputs width count bound
        builder candidates) := by
  induction candidates generalizing state builder with
  | nil =>
      have hconstant :=
        selectiveConst_matches state builder false hmatches
      exact ⟨hconstant.1, hconstant.2⟩
  | cons candidate rest inductionHypothesis =>
      let rawHead :=
        selectiveCompileTableFixedCount outputs width count bound
          state candidate
      let head :=
        compileTableFixedCount outputs width count bound
          builder candidate
      have hhead : rawHead.MatchesBuilt head :=
        selectiveCompileTableFixedCount_matches outputs width count bound
          state builder candidate hmatches
      let rawTail :=
        selectiveCompileTableCountCases outputs width count bound
          rawHead.state rest
      let tail :=
        compileTableCountCases outputs width count bound
          head.compiled.final rest
      have htail : rawTail.MatchesBuilt tail :=
        inductionHypothesis rawHead.state head.compiled.final hhead.1
      let headAtTail :=
        head.live.lift tail.compiled.extension
      let rawDisjunction :=
        selectiveOr rawTail.state rawHead.output rawTail.output
      let disjunction :=
        compileOr tail.compiled.final headAtTail tail.live
      have hdisjunction : rawDisjunction.Matches disjunction :=
        selectiveOr_matches rawTail.state tail.compiled.final
          rawHead.output rawTail.output headAtTail tail.live htail.1
          (by
            simpa [headAtTail, LiveWire.lift, BuiltWire.live] using
              hhead.2)
          htail.2
      constructor
      · simpa [selectiveCompileTableCountCases,
          compileTableCountCases, rawHead, head, rawTail, tail,
          headAtTail, rawDisjunction, disjunction,
          BuiltWire.ofCompiled, CompiledWire.prepend] using
          hdisjunction.1
      · simpa [selectiveCompileTableCountCases,
          compileTableCountCases, rawHead, head, rawTail, tail,
          headAtTail, rawDisjunction, disjunction,
          BuiltWire.ofCompiled, CompiledWire.prepend] using
          hdisjunction.2

theorem selectiveCompileTableBoundedOracleVerifier_matches
    (outputs : List ℕ) (width count bound target : ℕ) :
    (selectiveCompileTableBoundedOracleVerifier
        outputs width count bound target).MatchesBuilt
      (compileTableBoundedOracleVerifier outputs width count bound <|
        BooleanDAGBuilder.empty (descriptionWidth width bound)) := by
  exact selectiveCompileTableCountCases_matches outputs width count bound
    (SelectiveState.empty (descriptionWidth width bound) target)
    (BooleanDAGBuilder.empty (descriptionWidth width bound))
    (List.ofFn id)
    (SelectiveState.empty_matches
      (descriptionWidth width bound) target)

/-! The selected offset is immutable compiler context.  Keeping this as a
separate invariant avoids storing it redundantly in every wire relation. -/

@[simp] theorem SelectiveState.emit_target {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n) :
    (state.emit node).state.target = state.target :=
  rfl

@[simp] theorem selectiveConst_target {n : ℕ}
    (state : SelectiveState n) (value : Bool) :
    (selectiveConst state value).state.target = state.target :=
  rfl

@[simp] theorem selectiveInput_target {n : ℕ}
    (state : SelectiveState n) (index : Fin n) :
    (selectiveInput state index).state.target = state.target :=
  rfl

@[simp] theorem selectiveNot_target {n : ℕ}
    (state : SelectiveState n) (child : ℕ) :
    (selectiveNot state child).state.target = state.target :=
  rfl

@[simp] theorem selectiveAnd_target {n : ℕ}
    (state : SelectiveState n) (left right : ℕ) :
    (selectiveAnd state left right).state.target = state.target :=
  rfl

@[simp] theorem selectiveOr_target {n : ℕ}
    (state : SelectiveState n) (left right : ℕ) :
    (selectiveOr state left right).state.target = state.target :=
  rfl

@[simp] theorem selectiveCompileExpr_target {n : ℕ}
    (state : SelectiveState n) (expression : BoolExpr n) :
    (selectiveCompileExpr state expression).state.target =
      state.target := by
  induction expression generalizing state <;>
    simp [selectiveCompileExpr, *]

@[simp] theorem selectiveCompileGuardedAny_target {n : ℕ}
    (state : SelectiveState n) (choices : List (BoolExpr n × ℕ)) :
    (selectiveCompileGuardedAny state choices).state.target =
      state.target := by
  induction choices generalizing state with
  | nil =>
      simpa only [selectiveCompileGuardedAny] using
        selectiveConst_target state false
  | cons choice rest inductionHypothesis =>
      simp [selectiveCompileGuardedAny, inductionHypothesis]

@[simp] theorem selectiveCompileFieldSelect_target {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List ℕ) :
    (selectiveCompileFieldSelect state fieldEquals row values).state.target =
      state.target := by
  simp [selectiveCompileFieldSelect]

@[simp] theorem selectiveCompileUniversalNode_target {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n)
    (values : List ℕ) :
    (selectiveCompileUniversalNode state row address values).state.target =
      state.target := by
  simp [selectiveCompileUniversalNode,
    selectiveCompileFirstFieldSelect,
    selectiveCompileSecondFieldSelect]

@[simp] theorem selectiveCompileUniversalNodes_target {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (selectiveCompileUniversalNodes state address count hcount).state.target =
      state.target := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp [selectiveCompileUniversalNodes, inductionHypothesis]

@[simp] theorem selectiveCompileUniversalOutput_target {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (selectiveCompileUniversalOutput state address count hcount).state.target =
      state.target := by
  simp [selectiveCompileUniversalOutput,
    selectiveCompileFirstFieldSelect]

@[simp] theorem selectiveCompileUniversalOutputs_target {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound)
    (addresses : List (BitInput n)) :
    (selectiveCompileUniversalOutputs state count hcount
      addresses).state.target = state.target := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address rest inductionHypothesis =>
      simp [selectiveCompileUniversalOutputs, inductionHypothesis]

@[simp] theorem selectiveCompileLiteral_target {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (literal : Literal q) :
    (selectiveCompileLiteral state values literal).state.target =
      state.target := by
  cases literal <;> rfl

@[simp] theorem selectiveCompileClause_target {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (clause : Fin 3 → Literal q) :
    (selectiveCompileClause state values clause).state.target =
      state.target := by
  simp [selectiveCompileClause]

@[simp] theorem selectiveCompileClauses_target {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (clauses : List (Fin 3 → Literal q)) :
    (selectiveCompileClauses state values clauses).state.target =
      state.target := by
  induction clauses generalizing state with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      simp [selectiveCompileClauses, inductionHypothesis]

@[simp] theorem selectiveCompileTableVerifierRow_target
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCode : ℕ) :
    (selectiveCompileTableVerifierRow outputs width count bound state
      nodeCount hnodeCount randomnessCode).state.target =
        state.target := by
  simp [selectiveCompileTableVerifierRow]

@[simp] theorem selectiveCompileTableVerifierRows_target
    (outputs : List ℕ) (width count bound : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound))
    (randomnessCodes : List ℕ) :
    (selectiveCompileTableVerifierRows outputs width count bound
      nodeCount hnodeCount state randomnessCodes).state.target =
        state.target := by
  induction randomnessCodes generalizing state with
  | nil => rfl
  | cons randomnessCode rest inductionHypothesis =>
      simp [selectiveCompileTableVerifierRows, inductionHypothesis]

@[simp] theorem selectiveCompileTableFixedCount_target
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) :
    (selectiveCompileTableFixedCount outputs width count bound
      state candidate).state.target = state.target := by
  simp [selectiveCompileTableFixedCount]

@[simp] theorem selectiveCompileTableCountCases_target
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) :
    (selectiveCompileTableCountCases outputs width count bound
      state candidates).state.target = state.target := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      simp [selectiveCompileTableCountCases, inductionHypothesis]

@[simp] theorem selectiveCompileTableBoundedOracleVerifier_target
    (outputs : List ℕ) (width count bound target : ℕ) :
    (selectiveCompileTableBoundedOracleVerifier
      outputs width count bound target).state.target = target := by
  simp [selectiveCompileTableBoundedOracleVerifier,
    SelectiveState.empty]

theorem selectiveStructuralFormulaResponse_eq
    (outputs : List ℕ) (width count bound index : ℕ) :
    selectiveStructuralFormulaResponse outputs width count bound index =
      (tableBoundedOracleStructuralFormulaLength
          outputs width count bound,
        tableBoundedOracleStructuralFormulaAtomAt
          outputs width count bound index) := by
  let inputArity := descriptionWidth width bound
  let target := index - inputArity
  let raw :=
    selectiveCompileTableBoundedOracleVerifier
      outputs width count bound target
  let compiled :=
    compileTableBoundedOracleVerifier outputs width count bound <|
      BooleanDAGBuilder.empty inputArity
  have hrefinement : raw.MatchesBuilt compiled :=
    selectiveCompileTableBoundedOracleVerifier_matches
      outputs width count bound target
  have hschedule :
      tableBoundedOracleStructuralNodeSchedule outputs width count bound =
        compiled.compiled.final.nodes := by
    rw [tableBoundedOracleStructuralNodeSchedule_eq_nodes]
    rfl
  have hnext :
      raw.state.next =
        (tableBoundedOracleStructuralNodeSchedule
          outputs width count bound).length := by
    calc
      raw.state.next = compiled.compiled.final.nodes.length :=
        hrefinement.1.1
      _ = _ := congrArg List.length hschedule.symm
  have hselected :
      raw.state.selected =
        (tableBoundedOracleStructuralNodeSchedule
          outputs width count bound)[target]? := by
    have htarget : raw.state.target = target := by
      simp [raw]
    calc
      raw.state.selected =
          compiled.compiled.final.nodes[raw.state.target]? :=
        hrefinement.1.2
      _ = compiled.compiled.final.nodes[target]? := by rw [htarget]
      _ = _ := congrArg (fun nodes => nodes[target]?) hschedule.symm
  have houtput :
      raw.output =
        tableBoundedOracleStructuralOutputIndex
          outputs width count bound := by
    calc
      raw.output = compiled.compiled.output.val := hrefinement.2
      _ = _ := rfl
  apply Prod.ext
  · simp [selectiveStructuralFormulaResponse,
      tableBoundedOracleStructuralFormulaLength, inputArity, target,
      raw, hnext]
  · by_cases hinput : index < inputArity
    · simp [selectiveStructuralFormulaResponse,
        tableBoundedOracleStructuralFormulaAtomAt,
        structuralFormulaAtomAtSchedule, inputArity,
        hinput]
    · simp only [selectiveStructuralFormulaResponse,
        tableBoundedOracleStructuralFormulaAtomAt,
        structuralFormulaAtomAtSchedule, inputArity,
        if_neg hinput]
      rw [hselected, houtput]
      have hinput' :
          ¬index < descriptionWidth width bound := by
        simpa [inputArity] using hinput
      simp only [dif_neg hinput']
      dsimp only [target, inputArity]
      cases hlookup :
          (tableBoundedOracleStructuralNodeSchedule
            outputs width count bound)[
              index - descriptionWidth width bound]? <;>
        simp

end NearCubicWires.BoundedOracleStructuralSelectiveCompiler

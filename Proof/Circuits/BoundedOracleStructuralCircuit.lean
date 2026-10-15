import Proof.Circuits.CircuitInputCNF
import Proof.Circuits.FinitePredicateCircuit
import Proof.Foundations.OuterPCPRecovery

/-!
# Polynomial structural circuit for bounded oracle descriptions

The C.12 SAT variables are the fixed unary rows from
`canonicalBoundedCircuitDescription`.  This module compiles those rows
directly.  It never enumerates Boolean functions or bounded circuits: every
gate is charged to a row, unary field position, candidate node count, verifier
row, or oracle query.
-/

namespace NearCubicWires.BoundedOracleStructuralCircuit

open NearCubicWires
open NearCubicWires.CircuitInputCNF
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TseitinCNF

abbrev rowWidth (n bound : ℕ) : ℕ :=
  6 + 2 * boundedCircuitFieldLimit n bound

abbrev descriptionWidth (n bound : ℕ) : ℕ :=
  boundedCircuitDescriptionWidth n bound

def descriptionIndex {n bound : ℕ}
    (row : Fin (bound + 1)) (offset : Fin (rowWidth n bound)) :
    Fin (descriptionWidth n bound) :=
  ⟨row.val * rowWidth n bound + offset.val, by
    unfold descriptionWidth boundedCircuitDescriptionWidth
    calc
      row.val * rowWidth n bound + offset.val <
          row.val * rowWidth n bound + rowWidth n bound :=
        Nat.add_lt_add_left offset.isLt _
      _ = (row.val + 1) * rowWidth n bound := by ring
      _ ≤ (bound + 1) * rowWidth n bound :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr row.isLt)⟩

def unaryEqualsExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.all <| List.ofFn fun offset : Fin limit =>
    let index := descriptionIndex row
      ⟨start + offset.val, by omega⟩
    if offset.val < value then
      .input index
    else
      .not (.input index)

def tagEqualsExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  unaryEqualsExpr row 0 6 value (by simp [rowWidth])

def firstFieldEqualsExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  unaryEqualsExpr row 6 (boundedCircuitFieldLimit n bound) value
    (by
      simp [rowWidth]
      omega)

def secondFieldEqualsExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (value : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  unaryEqualsExpr row
    (6 + boundedCircuitFieldLimit n bound)
    (boundedCircuitFieldLimit n bound) value (by
      simp [rowWidth]
      omega)

def firstFieldLessExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.any <|
    (List.range upper).map (firstFieldEqualsExpr row)

def secondFieldLessExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.any <|
    (List.range upper).map (secondFieldEqualsExpr row)

def nodeRowExpr {n bound : ℕ}
    (row : Fin (bound + 1)) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.any
    [ BoolExpr.all
        [tagEqualsExpr row 0,
          BoolExpr.any
            [firstFieldEqualsExpr row 0,
              firstFieldEqualsExpr row 1],
          secondFieldEqualsExpr row 0]
    , BoolExpr.all
        [tagEqualsExpr row 1,
          firstFieldLessExpr row n,
          secondFieldEqualsExpr row 0]
    , BoolExpr.all
        [tagEqualsExpr row 2,
          firstFieldLessExpr row row.val,
          secondFieldEqualsExpr row 0]
    , BoolExpr.all
        [tagEqualsExpr row 3,
          firstFieldLessExpr row row.val,
          secondFieldLessExpr row row.val]
    , BoolExpr.all
        [tagEqualsExpr row 4,
          firstFieldLessExpr row row.val,
          secondFieldLessExpr row row.val]
    ]

def outputRowExpr {n bound : ℕ}
    (row : Fin (bound + 1)) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.all
    [tagEqualsExpr row 5,
      firstFieldLessExpr row row.val,
      secondFieldEqualsExpr row 0]

def paddingRowExpr {n bound : ℕ}
    (row : Fin (bound + 1)) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.all
    [tagEqualsExpr row 6,
      firstFieldEqualsExpr row 0,
      secondFieldEqualsExpr row 0]

def countNodeRows {n bound : ℕ} (count : Fin bound) :
    List (BoolExpr (descriptionWidth n bound)) :=
  List.ofFn fun index : Fin (count.val + 1) =>
    nodeRowExpr
      ⟨index.val, by
        have hcount := count.isLt
        have hindex := index.isLt
        omega⟩

def countPaddingRows {n bound : ℕ} (count : Fin bound) :
    List (BoolExpr (descriptionWidth n bound)) :=
  List.ofFn fun offset : Fin (bound - (count.val + 1)) =>
    paddingRowExpr
      ⟨count.val + 2 + offset.val, by
        have hcount := count.isLt
        have hoffset := offset.isLt
        omega⟩

def fixedCountGrammarExpr {n bound : ℕ} (count : Fin bound) :
    BoolExpr (descriptionWidth n bound) :=
  let outputRow : Fin (bound + 1) :=
    ⟨count.val + 1, by omega⟩
  BoolExpr.all <|
    countNodeRows count ++
      outputRowExpr outputRow :: countPaddingRows count

def boundedGrammarExpr (n bound : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.any <| List.ofFn fun count : Fin bound =>
    fixedCountGrammarExpr count

def grammarCircuit (n bound : ℕ) :
    BooleanCircuit (descriptionWidth n bound) :=
  let compiled :=
    compileExpr (BooleanDAGBuilder.empty (descriptionWidth n bound))
      (boundedGrammarExpr n bound)
  compiled.final.finish compiled.output

@[simp] theorem grammarCircuit_eval (n bound : ℕ)
    (description : BitInput (descriptionWidth n bound)) :
    (grammarCircuit n bound).eval description =
      (boundedGrammarExpr n bound).eval description := by
  let compiled :=
    compileExpr (BooleanDAGBuilder.empty (descriptionWidth n bound))
      (boundedGrammarExpr n bound)
  change
    (compiled.final.finish compiled.output).eval description =
      (boundedGrammarExpr n bound).eval description
  rw [BooleanDAGBuilder.finish_eval]
  have hcorrect := congrArg (fun value => value.getD false)
    (compiled.correct description)
  exact hcorrect

@[simp] theorem unaryEqualsExpr_eval {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (description : BitInput (descriptionWidth n bound)) :
    (unaryEqualsExpr row start limit value hblock).eval description =
      (List.ofFn fun offset : Fin limit =>
        description (descriptionIndex row
          ⟨start + offset.val, by omega⟩) ==
            decide (offset.val < value)).all id := by
  rw [unaryEqualsExpr, BoolExpr.eval_all]
  have hmap :
      (List.ofFn fun offset : Fin limit =>
          let index := descriptionIndex row
            ⟨start + offset.val, by omega⟩
          if offset.val < value then
            BoolExpr.input index
          else
            BoolExpr.not (BoolExpr.input index)).map
          (fun expression => expression.eval description) =
        List.ofFn fun offset : Fin limit =>
          description (descriptionIndex row
            ⟨start + offset.val, by omega⟩) ==
              decide (offset.val < value) := by
    apply List.ext_getElem
    · simp
    · intro index hleft hright
      simp only [List.length_map, List.length_ofFn] at hleft hright
      simp only [List.getElem_map, List.getElem_ofFn]
      split <;> rename_i hvalue
      · simp only [BoolExpr.eval]
        simp [hvalue]
      · cases hbit :
            description (descriptionIndex row
              ⟨start + index, by omega⟩) <;>
          simp only [BoolExpr.eval, hbit, Bool.not_false, Bool.not_true] <;>
          simp [hvalue]
  rw [← hmap, List.all_map]
  rfl

def selectFunctions {n bound : ℕ}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (functions : List (BoolFunction (descriptionWidth n bound)))
    (description : BitInput (descriptionWidth n bound)) : Bool :=
  functions.zipIdx.any fun entry =>
    (fieldEquals row entry.2).eval description &&
      entry.1 description

def fieldChoices {n bound : ℕ}
    {builder : BooleanDAGBuilder (descriptionWidth n bound)}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder)) :
    List (GuardedChoice builder) :=
  values.zipIdx.map fun entry =>
    { condition := fieldEquals row entry.2
      value := entry.1 }

def selectLiveWires {n bound : ℕ}
    {builder : BooleanDAGBuilder (descriptionWidth n bound)}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder))
    (description : BitInput (descriptionWidth n bound)) : Bool :=
  values.zipIdx.any fun entry =>
    (fieldEquals row entry.2).eval description &&
      entry.1.function description

def compileFieldSelect {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder)) :
    CompiledWire builder
      (selectLiveWires fieldEquals row values) := by
  let compiled := compileGuardedAny builder
    (fieldChoices fieldEquals row values)
  exact
    { final := compiled.final
      extension := compiled.extension
      output := compiled.output
      correct := by
        intro input
        rw [compiled.correct]
        congr 1
        simp [fieldChoices, GuardedChoice.eval,
          selectLiveWires, List.any_map, Function.comp_def] }

def compileFirstFieldSelect {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder)) :
    CompiledWire builder
      (selectLiveWires firstFieldEqualsExpr row values) :=
  compileFieldSelect builder firstFieldEqualsExpr row values

def compileSecondFieldSelect {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder)) :
    CompiledWire builder
      (selectLiveWires secondFieldEqualsExpr row values) :=
  compileFieldSelect builder secondFieldEqualsExpr row values

def liftLiveWires {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (values : List (LiveWire prior)) : List (LiveWire final) :=
  values.map (LiveWire.lift extension)

@[simp] theorem liftLiveWires_length {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (values : List (LiveWire prior)) :
    (liftLiveWires extension values).length = values.length := by
  simp [liftLiveWires]

@[simp] theorem liftLiveWires_functions {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (values : List (LiveWire prior)) :
    (liftLiveWires extension values).map LiveWire.function =
      values.map LiveWire.function := by
  simp [liftLiveWires]

def constantAddressSelectionExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (address : BitInput n) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.any <| List.ofFn fun index : Fin n =>
    if address index then
      firstFieldEqualsExpr row index.val
    else
      .const false

def selectFunctionValues {n bound : ℕ}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (values : List (BoolFunction (descriptionWidth n bound)))
    (description : BitInput (descriptionWidth n bound)) : Bool :=
  values.zipIdx.any fun entry =>
    (fieldEquals row entry.2).eval description &&
      entry.1 description

@[simp] theorem selectLiveWires_eq_selectFunctionValues
    {n bound : ℕ}
    {builder :
      BooleanDAGBuilder (descriptionWidth n bound)}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (values : List (LiveWire builder))
    (description : BitInput (descriptionWidth n bound)) :
    selectLiveWires fieldEquals row values description =
      selectFunctionValues fieldEquals row
        (values.map LiveWire.function) description := by
  simp [selectLiveWires, selectFunctionValues, List.zipIdx_map,
    List.any_map, Function.comp_def]

/-- Pure semantics of one described DAG row.  This definition is independent
of the builder and is the specification compiled by `compileUniversalNode`. -/
def universalNodeValue {n bound : ℕ}
    (row : Fin (bound + 1)) (address : BitInput n)
    (priorValues :
      List (BoolFunction (descriptionWidth n bound)))
    (description : BitInput (descriptionWidth n bound)) : Bool :=
  let left :=
    selectFunctionValues firstFieldEqualsExpr row priorValues
      description
  let right :=
    selectFunctionValues secondFieldEqualsExpr row priorValues
      description
  let constantValue :=
    (firstFieldEqualsExpr row 1).eval description
  let inputValue :=
    (constantAddressSelectionExpr row address).eval description
  let cases :=
    [ (tagEqualsExpr row 0).eval description && constantValue
    , (tagEqualsExpr row 1).eval description && inputValue
    , (tagEqualsExpr row 2).eval description && !left
    , (tagEqualsExpr row 3).eval description && (left && right)
    , (tagEqualsExpr row 4).eval description && (left || right)
    ]
  cases.any id

def universalNodeValues {n bound : ℕ}
    (address : BitInput n) :
    (count : ℕ) → count ≤ bound →
      List (BoolFunction (descriptionWidth n bound))
  | 0, _ => []
  | count + 1, hcount =>
      let earlier :=
        universalNodeValues address count (by omega)
      let row : Fin (bound + 1) := ⟨count, by omega⟩
      earlier ++ [universalNodeValue row address earlier]

@[simp] theorem universalNodeValues_length {n bound : ℕ}
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (universalNodeValues address count hcount).length = count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp only [universalNodeValues, List.length_append,
        List.length_singleton, inductionHypothesis]

def universalOutputValue {n bound : ℕ}
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (description : BitInput (descriptionWidth n bound)) : Bool :=
  let values := universalNodeValues address count hcount
  let outputRow : Fin (bound + 1) := ⟨count, by omega⟩
  selectFunctionValues firstFieldEqualsExpr outputRow values
    description

/-- Compile one row of the universal Boolean-DAG evaluator.  The prior node
values remain shared wires; selecting a child is linear in the row index and
never expands the child computation. -/
def compileUniversalNode {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n)
    (priorValues : List (LiveWire builder)) :
    BuiltWire builder :=
  let left := compileFirstFieldSelect builder row priorValues
  let valuesAtLeft := liftLiveWires left.extension priorValues
  let right := compileSecondFieldSelect left.final row valuesAtLeft
  let leftAtRight := left.live.lift right.extension
  let constantValue :=
    compileExpr right.final (firstFieldEqualsExpr row 1)
  let leftAtConstant := leftAtRight.lift constantValue.extension
  let rightAtConstant := right.live.lift constantValue.extension
  let inputValue :=
    compileExpr constantValue.final
      (constantAddressSelectionExpr row address)
  let leftAtInput := leftAtConstant.lift inputValue.extension
  let rightAtInput := rightAtConstant.lift inputValue.extension
  let negated := compileNot inputValue.final leftAtInput
  let leftAtNegated := leftAtInput.lift negated.extension
  let rightAtNegated := rightAtInput.lift negated.extension
  let conjunction :=
    compileAnd negated.final leftAtNegated rightAtNegated
  let leftAtConjunction := leftAtNegated.lift conjunction.extension
  let rightAtConjunction := rightAtNegated.lift conjunction.extension
  let disjunction :=
    compileOr conjunction.final leftAtConjunction rightAtConjunction
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
  let selected := compileGuardedAny disjunction.final choices
  let result := selected.prepend caseExtension
  { function :=
      universalNodeValue row address
        (priorValues.map LiveWire.function)
    compiled :=
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro description
          rw [result.correct]
          congr 1
          simp [choices, GuardedChoice.eval, universalNodeValue,
            constantValue, inputValue, negated, conjunction,
            disjunction, leftAtInput, rightAtInput, leftAtNegated,
            rightAtNegated, leftAtConjunction, rightAtConjunction,
            leftAtConstant, rightAtConstant, leftAtRight, left, right,
            valuesAtLeft, liftLiveWires, selectLiveWires,
            selectFunctionValues, List.zipIdx_map, List.any_map,
            Function.comp_def] } }

@[simp] theorem compileUniversalNode_function {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n)
    (priorValues : List (LiveWire builder)) :
    (compileUniversalNode builder row address priorValues).function =
      universalNodeValue row address
        (priorValues.map LiveWire.function) := by
  rfl

structure CompiledNodeTable {n : ℕ}
    (prior : BooleanDAGBuilder n) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  values : List (LiveWire final)

def compileUniversalNodes {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) :
    (count : ℕ) → count ≤ bound → CompiledNodeTable builder
  | 0, _ =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        values := [] }
  | count + 1, hcount =>
      let earlier := compileUniversalNodes builder address count (by omega)
      let row : Fin (bound + 1) := ⟨count, by omega⟩
      let node :=
        compileUniversalNode earlier.final row address earlier.values
      { final := node.compiled.final
        extension := earlier.extension.trans node.compiled.extension
        values :=
          liftLiveWires node.compiled.extension earlier.values ++
            [node.live] }

@[simp] theorem compileUniversalNodes_values_length {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (compileUniversalNodes builder address count hcount).values.length =
      count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp only [compileUniversalNodes, List.length_append,
        List.length_singleton, liftLiveWires, List.length_map,
        inductionHypothesis]

@[simp] theorem compileUniversalNodes_functions {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (compileUniversalNodes builder address count hcount).values.map
        LiveWire.function =
      universalNodeValues address count hcount := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      simp only [compileUniversalNodes, universalNodeValues,
        List.map_append, List.map_singleton, liftLiveWires_functions,
        inductionHypothesis, BuiltWire.live_function,
        compileUniversalNode_function]

def compileUniversalOutput {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    BuiltWire builder :=
  let nodes := compileUniversalNodes builder address count hcount
  let outputRow : Fin (bound + 1) := ⟨count, by omega⟩
  let selected :=
    compileFirstFieldSelect nodes.final outputRow nodes.values
  let result := selected.prepend nodes.extension
  { function := universalOutputValue address count hcount
    compiled :=
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro description
          rw [result.correct]
          congr 1
          rw [selectLiveWires_eq_selectFunctionValues,
            compileUniversalNodes_functions]
          rfl } }

@[simp] theorem compileUniversalOutput_function {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (compileUniversalOutput builder address count hcount).function =
      universalOutputValue address count hcount := by
  rfl

structure CompiledWireList {n : ℕ}
    (prior : BooleanDAGBuilder n) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  values : List (LiveWire final)

def compileUniversalOutputs {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound) :
    List (BitInput n) → CompiledWireList builder
  | [] =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        values := [] }
  | address :: rest =>
      let head := compileUniversalOutput builder address count hcount
      let tail :=
        compileUniversalOutputs head.compiled.final count hcount rest
      { final := tail.final
        extension := head.compiled.extension.trans tail.extension
        values := head.live.lift tail.extension :: tail.values }

@[simp] theorem compileUniversalOutputs_values_length {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound)
    (addresses : List (BitInput n)) :
    (compileUniversalOutputs builder count hcount addresses).values.length =
      addresses.length := by
  induction addresses generalizing builder with
  | nil =>
      rfl
  | cons address rest inductionHypothesis =>
      simp only [compileUniversalOutputs, List.length_cons,
        inductionHypothesis]

@[simp] theorem compileUniversalOutputs_functions {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound)
    (addresses : List (BitInput n)) :
    (compileUniversalOutputs builder count hcount addresses).values.map
        LiveWire.function =
      addresses.map fun address =>
        universalOutputValue address count hcount := by
  induction addresses generalizing builder with
  | nil =>
      rfl
  | cons address rest inductionHypothesis =>
      simp only [compileUniversalOutputs, List.map_cons,
        LiveWire.lift_function, BuiltWire.live_function,
        compileUniversalOutput_function, inductionHypothesis]

def literalWire {q : ℕ} {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q) :
    Literal q → LiveWire builder
  | .positive query =>
      values[query.val]'(by simp [hlength])
  | .negative query =>
      values[query.val]'(by simp [hlength])

def liveAssignment {q : ℕ} {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (input : BitInput n) : BitInput q :=
  fun query =>
    (literalWire values hlength (.positive query)).function input

@[simp] theorem liveAssignment_lift {q : ℕ} {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (values : List (LiveWire prior))
    (hlength : values.length = q)
    (liftedLength : (liftLiveWires extension values).length = q) :
    liveAssignment (liftLiveWires extension values) liftedLength =
      liveAssignment values hlength := by
  funext input query
  simp [liveAssignment, literalWire, liftLiveWires]

theorem liveAssignment_compileUniversalOutputs
    {n bound q : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound)
    (addresses : List (BitInput n))
    (haddresses : addresses.length = q)
    (hlength :
      (compileUniversalOutputs builder count hcount addresses).values.length =
        q)
    (description : BitInput (descriptionWidth n bound)) :
    liveAssignment
        (compileUniversalOutputs builder count hcount addresses).values
        hlength description =
      fun query : Fin q =>
        universalOutputValue
          (addresses[query.val]'(by
            simpa only [haddresses] using query.isLt))
          count hcount description := by
  funext query
  have hfunctions :=
    congrArg (fun functions =>
      functions[query.val]?.getD fun _ => false)
      (compileUniversalOutputs_functions builder count hcount addresses)
  have hatInput := congrFun hfunctions description
  have hvaluesBound :
      query.val <
        (compileUniversalOutputs builder count hcount addresses).values.length := by
    rw [hlength]
    exact query.isLt
  have haddressesBound : query.val < addresses.length := by
    rw [haddresses]
    exact query.isLt
  simp only [List.getElem?_map] at hatInput
  rw [List.getElem?_eq_getElem hvaluesBound,
    List.getElem?_eq_getElem haddressesBound] at hatInput
  simpa only [liveAssignment, literalWire, Option.map_some,
    Option.getD_some, List.getElem_map] using hatInput

def compileLiteral {q : ℕ} {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q) :
    Literal q → BuiltWire builder
  | .positive query =>
      BuiltWire.ofCompiled <|
        (literalWire values hlength (.positive query)).stationary
  | .negative query =>
      BuiltWire.ofCompiled <|
        compileNot builder (literalWire values hlength (.negative query))

@[simp] theorem compileLiteral_function {q : ℕ} {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (literal : Literal q) :
    (compileLiteral builder values hlength literal).function =
      fun input => literal.eval (liveAssignment values hlength input) := by
  cases literal <;> rfl

def clauseValue {q : ℕ} {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clause : Fin 3 → Literal q) (input : BitInput n) : Bool :=
  (clause 0).eval (liveAssignment values hlength input) ||
    (clause 1).eval (liveAssignment values hlength input) ||
      (clause 2).eval (liveAssignment values hlength input)

def compileClause {q : ℕ} {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clause : Fin 3 → Literal q) : BuiltWire builder :=
  let first := compileLiteral builder values hlength (clause 0)
  let valuesAtFirst := liftLiveWires first.compiled.extension values
  let valuesAtFirstLength : valuesAtFirst.length = q := by
    dsimp only [valuesAtFirst]
    rw [liftLiveWires_length]
    exact hlength
  let second := compileLiteral first.compiled.final valuesAtFirst
    valuesAtFirstLength
    (clause 1)
  let firstAtSecond := first.live.lift second.compiled.extension
  let firstOrSecond :=
    compileOr second.compiled.final firstAtSecond second.live
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
  let third := compileLiteral firstOrSecond.final valuesAtDisjunction
    valuesAtDisjunctionLength
    (clause 2)
  let disjunctionAtThird :=
    firstOrSecond.live.lift third.compiled.extension
  let output :=
    compileOr third.compiled.final disjunctionAtThird third.live
  let result := output.prepend <|
    first.compiled.extension.trans <|
      second.compiled.extension.trans <|
        firstOrSecond.extension.trans third.compiled.extension
  { function := clauseValue values hlength clause
    compiled :=
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro input
          rw [result.correct]
          congr 1
          change
            (firstOrSecond.live.function input ||
                third.function input) =
              clauseValue values hlength clause input
          rw [CompiledWire.live_function]
          change
            ((first.function input || second.function input) ||
                third.function input) =
              clauseValue values hlength clause input
          simp only [first, second, third,
            compileLiteral_function]
          rw [liveAssignment_lift
              first.compiled.extension values hlength
              valuesAtFirstLength,
            liveAssignment_lift
              (first.compiled.extension.trans <|
                second.compiled.extension.trans
                  firstOrSecond.extension)
              values hlength valuesAtDisjunctionLength]
          rfl } }

@[simp] theorem compileClause_function {q : ℕ} {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clause : Fin 3 → Literal q) :
    (compileClause builder values hlength clause).function =
      clauseValue values hlength clause := by
  rfl

def clausesValue {q : ℕ} {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clauses : List (Fin 3 → Literal q))
    (input : BitInput n) : Bool :=
  clauses.all fun clause => clauseValue values hlength clause input

theorem clauseValue_eq_decide_exists {q : ℕ} {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clause : Fin 3 → Literal q) (input : BitInput n) :
    clauseValue values hlength clause input =
      decide (∃ index,
        (clause index).eval (liveAssignment values hlength input) =
          true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [clauseValue, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((hzero | hone) | htwo)
    · exact ⟨0, hzero⟩
    · exact ⟨1, hone⟩
    · exact ⟨2, htwo⟩
  · rintro ⟨index, hindex⟩
    fin_cases index
    · exact Or.inl (Or.inl hindex)
    · exact Or.inl (Or.inr hindex)
    · exact Or.inr hindex

theorem clausesValue_eq_threeCNF {q : ℕ} {n : ℕ}
    {builder : BooleanDAGBuilder n}
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (formula : ThreeCNF q) (input : BitInput n) :
    clausesValue values hlength formula.clauses input =
      formula.eval (liveAssignment values hlength input) := by
  unfold clausesValue ThreeCNF.eval
  apply congrArg
  funext clause
  exact clauseValue_eq_decide_exists values hlength clause input

def compileClauses {q : ℕ} {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q) :
    (clauses : List (Fin 3 → Literal q)) →
      CompiledWire builder (clausesValue values hlength clauses)
  | [] =>
      compileConst builder true
  | clause :: rest =>
      let head := compileClause builder values hlength clause
      let valuesAtHead :=
        liftLiveWires head.compiled.extension values
      let valuesAtHeadLength : valuesAtHead.length = q := by
        dsimp only [valuesAtHead]
        rw [liftLiveWires_length]
        exact hlength
      let tail :=
        compileClauses head.compiled.final valuesAtHead
          valuesAtHeadLength
          rest
      let headAtTail := head.live.lift tail.extension
      let conjunction :=
        compileAnd tail.final headAtTail tail.live
      let result := conjunction.prepend <|
        head.compiled.extension.trans tail.extension
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro input
          rw [result.correct]
          congr 1
          change
            (clauseValue values hlength clause input &&
                clausesValue valuesAtHead valuesAtHeadLength rest input) =
              clausesValue values hlength (clause :: rest) input
          have hassignment :
              liveAssignment valuesAtHead valuesAtHeadLength =
                liveAssignment values hlength :=
            liveAssignment_lift head.compiled.extension values hlength
              valuesAtHeadLength
          simp [clausesValue, clauseValue, hassignment] }

def allRandomness (width : ℕ) : List (BitInput width) :=
  (List.range (2 ^ width)).map fun code bit =>
    code.testBit bit.val

@[simp] theorem allRandomness_length (width : ℕ) :
    (allRandomness width).length = 2 ^ width := by
  simp [allRandomness]

theorem mem_allRandomness {width : ℕ} (randomness : BitInput width) :
    randomness ∈ allRandomness width := by
  rw [allRandomness, List.mem_map]
  refine
    ⟨encodeBitInput randomness,
      List.mem_range.mpr ?_, ?_⟩
  · rw [encodeBitInput_eq_ofBits]
    exact Nat.ofBits_lt_two_pow randomness
  · funext bit
    rw [encodeBitInput_eq_ofBits]
    exact Nat.testBit_ofBits_lt randomness bit.val bit.isLt

def projectedAddresses
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    List (BitInput (pcp.nativeWidth n)) :=
  List.ofFn fun query =>
    projectedInput pcp input randomness query

@[simp] theorem projectedAddresses_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    (projectedAddresses pcp input randomness).length =
      pcp.queryCount n := by
  simp [projectedAddresses]

def describedQueryAssignment
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n))
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    BitInput (pcp.queryCount n) :=
  fun query =>
    universalOutputValue
      (projectedInput pcp input randomness query)
      count hcount description

def verifierRowValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n))
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    Bool :=
  (pcp.decision input randomness).eval <|
    describedQueryAssignment pcp input count hcount randomness
      description

/-- Compile one verifier row after evaluating every projected oracle query
through the same described DAG. -/
def compileVerifierRow
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) :
    BuiltWire builder :=
  let queries :=
    compileUniversalOutputs builder count hcount
      (projectedAddresses pcp input randomness)
  let queryLength : queries.values.length = pcp.queryCount n := by
    rw [compileUniversalOutputs_values_length,
      projectedAddresses_length]
  let decision :=
    compileClauses queries.final queries.values
      queryLength
      (pcp.decision input randomness).clauses
  let result := decision.prepend queries.extension
  { function :=
      verifierRowValue pcp input count hcount randomness
    compiled :=
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro description
          rw [result.correct]
          congr 1
          rw [clausesValue_eq_threeCNF]
          congr 1
          rw [liveAssignment_compileUniversalOutputs
            builder count hcount
            (projectedAddresses pcp input randomness)
            (projectedAddresses_length pcp input randomness)
            queryLength description]
          funext query
          simp [projectedAddresses, describedQueryAssignment] } }

@[simp] theorem compileVerifierRow_function
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) :
    (compileVerifierRow pcp input builder count hcount randomness).function =
      verifierRowValue pcp input count hcount randomness := by
  rfl

def verifierRowsValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (count : ℕ) (hcount : count ≤ bound)
    (randomnessRows : List (BitInput (pcp.nativeWidth n)))
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    Bool :=
  randomnessRows.all fun randomness =>
    verifierRowValue pcp input count hcount randomness description

def compileVerifierRows
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (count : ℕ) (hcount : count ≤ bound)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound)) :
    (randomnessRows : List (BitInput (pcp.nativeWidth n))) →
      CompiledWire builder
        (verifierRowsValue pcp input count hcount randomnessRows)
  | [] =>
      compileConst builder true
  | randomness :: rest =>
      let head :=
        compileVerifierRow pcp input builder count hcount randomness
      let tail :=
        compileVerifierRows pcp input count hcount
          head.compiled.final rest
      let headAtTail := head.live.lift tail.extension
      let conjunction :=
        compileAnd tail.final headAtTail tail.live
      let result := conjunction.prepend <|
        head.compiled.extension.trans tail.extension
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro description
          exact result.correct description }

/-- Direct Boolean predicate for one candidate node count. -/
def fixedCountValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : Fin bound)
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    Bool :=
  (fixedCountGrammarExpr
      (n := pcp.nativeWidth n) count).eval description &&
    verifierRowsValue pcp input (count.val + 1) (by omega)
      (allRandomness (pcp.nativeWidth n)) description

/-- Compile one exact node-count case.  The grammar guard and every verifier
row share one append-only DAG, so a successful assignment is simultaneously a
well-typed description and a universally accepting oracle circuit. -/
def compileFixedCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) :
    CompiledWire builder (fixedCountValue pcp input count) :=
  let grammar :=
    compileExpr builder
      (fixedCountGrammarExpr
        (n := pcp.nativeWidth n) count)
  let rows :=
    compileVerifierRows pcp input (count.val + 1) (by omega)
      grammar.final (allRandomness (pcp.nativeWidth n))
  let grammarAtRows := grammar.live.lift rows.extension
  let conjunction :=
    compileAnd rows.final grammarAtRows rows.live
  let result := conjunction.prepend <|
    grammar.extension.trans rows.extension
  { final := result.final
    extension := result.extension
    output := result.output
    correct := by
      intro description
      exact result.correct description }

def countCasesValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (counts : List (Fin bound))
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    Bool :=
  counts.any fun count =>
    fixedCountValue pcp input count description

def compileCountCases
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound)) :
    (counts : List (Fin bound)) →
      CompiledWire builder (countCasesValue pcp input counts)
  | [] =>
      compileConst builder false
  | count :: rest =>
      let head := compileFixedCount pcp input builder count
      let tail :=
        compileCountCases pcp input head.final rest
      let headAtTail := head.live.lift tail.extension
      let disjunction :=
        compileOr tail.final headAtTail tail.live
      let result := disjunction.prepend <|
        head.extension.trans tail.extension
      { final := result.final
        extension := result.extension
        output := result.output
        correct := by
          intro description
          exact result.correct description }

def boundedOraclePredicate
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ)
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    Bool :=
  countCasesValue pcp input (List.ofFn id) description

def compileBoundedOracleVerifier
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound)) :
    CompiledWire builder (boundedOraclePredicate pcp input bound) :=
  compileCountCases pcp input builder (List.ofFn id)

def boundedOracleVerifierCircuit
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    BooleanCircuit
      (descriptionWidth (pcp.nativeWidth n) bound) :=
  let compiled :=
    compileBoundedOracleVerifier pcp input bound <|
      BooleanDAGBuilder.empty
        (descriptionWidth (pcp.nativeWidth n) bound)
  compiled.final.finish compiled.output

@[simp] theorem boundedOracleVerifierCircuit_eval
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ)
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    (boundedOracleVerifierCircuit pcp input bound).eval description =
      boundedOraclePredicate pcp input bound description := by
  rw [boundedOracleVerifierCircuit,
    BooleanDAGBuilder.finish_eval]
  exact congrArg (fun value => value.getD false) <|
    (compileBoundedOracleVerifier pcp input bound <|
      BooleanDAGBuilder.empty
        (descriptionWidth (pcp.nativeWidth n) bound)).correct
      description

/-! ## Canonical-description semantics -/

theorem flatten_length_of_uniform {α : Type}
    (rows : List (List α)) (width : ℕ)
    (hwidth : ∀ row ∈ rows, row.length = width) :
    rows.flatten.length = rows.length * width := by
  induction rows with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      rw [List.flatten_cons, List.length_append,
        hwidth head (by simp), inductionHypothesis (by
          intro row hrow
          exact hwidth row (by simp [hrow])),
        List.length_cons]
      ring

theorem getElem_flatten_uniform {α : Type}
    (rows : List (List α)) (width rowIndex offset : ℕ)
    (hwidth : ∀ row ∈ rows, row.length = width)
    (hrow : rowIndex < rows.length) (hoffset : offset < width) :
    rows.flatten[rowIndex * width + offset]'(by
        rw [flatten_length_of_uniform rows width hwidth]
        calc
          rowIndex * width + offset <
              (rowIndex + 1) * width := by
            rw [Nat.add_mul]
            simp only [one_mul]
            omega
          _ ≤ rows.length * width :=
            Nat.mul_le_mul_right width
              (Nat.succ_le_iff.mpr hrow)) =
      (rows[rowIndex]'hrow)[offset]'(by
        rw [hwidth (rows[rowIndex]'hrow)
          (List.getElem_mem hrow)]
        exact hoffset) := by
  induction rows generalizing rowIndex with
  | nil =>
      simp at hrow
  | cons head tail inductionHypothesis =>
      have hhead : head.length = width :=
        hwidth head (by simp)
      have htail :
          ∀ row ∈ tail, row.length = width := by
        intro row hmember
        exact hwidth row (by simp [hmember])
      cases rowIndex with
      | zero =>
          simp only [List.flatten_cons, Nat.zero_mul, Nat.zero_add,
            List.getElem_cons_zero]
          apply List.getElem_append_left
      | succ rowIndex =>
          have htailRow : rowIndex < tail.length := by
            simpa only [List.length_cons,
              Nat.succ_lt_succ_iff] using hrow
          have hright :
              head.length ≤
                (rowIndex + 1) * width + offset := by
            rw [hhead]
            rw [Nat.add_mul]
            simp only [one_mul]
            omega
          simp only [List.flatten_cons, List.getElem_cons_succ]
          rw [List.getElem_append_right hright]
          have hindex :
              (rowIndex + 1) * width + offset - head.length =
                rowIndex * width + offset := by
            rw [hhead]
            rw [Nat.add_mul]
            simp only [one_mul]
            omega
          simpa only [hindex] using
            inductionHypothesis rowIndex htail htailRow

def canonicalDescriptionRows {n : ℕ}
    (bound : ℕ) (circuit : BooleanCircuit n) :
    List (List Bool) :=
  circuit.nodes.map (boundedNodeDescriptionBits bound) ++
    [boundedOutputDescriptionBits n bound circuit.output.val] ++
    List.replicate (bound - circuit.size)
      (boundedPaddingDescriptionBits n bound)

@[simp] theorem canonicalDescriptionRows_flatten {n : ℕ}
    (bound : ℕ) (circuit : BooleanCircuit n) :
    (canonicalDescriptionRows bound circuit).flatten =
      canonicalBoundedCircuitDescription bound circuit := by
  rfl

@[simp] theorem canonicalDescriptionRows_length {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    (canonicalDescriptionRows bound circuit).length = bound + 1 := by
  have hnodes : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  simp only [canonicalDescriptionRows, List.length_append,
    List.length_map, List.length_singleton, List.length_replicate,
    BooleanCircuit.size]
  omega

theorem canonicalDescriptionRows_uniform {n bound : ℕ}
    (circuit : BooleanCircuit n) :
    ∀ row ∈ canonicalDescriptionRows bound circuit,
      row.length = rowWidth n bound := by
  intro row hrow
  unfold canonicalDescriptionRows at hrow
  rcases List.mem_append.mp hrow with hprefix | hpadding
  · rcases List.mem_append.mp hprefix with hnode | houtput
    · rcases List.mem_map.mp hnode with ⟨node, _hnode, rfl⟩
      exact boundedNodeDescriptionBits_length node
    · rw [List.mem_singleton.mp houtput]
      exact
        boundedOutputDescriptionBits_length
          n bound circuit.output.val
  · rw [List.eq_of_mem_replicate hpadding]
    exact boundedPaddingDescriptionBits_length n bound

def canonicalDescriptionInput {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    BitInput (descriptionWidth n bound) :=
  fun index =>
    (canonicalBoundedCircuitDescription bound circuit)[index.val]'(by
      rw [canonicalBoundedCircuitDescription_length circuit hsize]
      exact index.isLt)

@[simp] theorem listOfFn_canonicalDescriptionInput
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    List.ofFn (canonicalDescriptionInput circuit hsize) =
      canonicalBoundedCircuitDescription bound circuit := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,
      canonicalBoundedCircuitDescription_length circuit hsize,
      descriptionWidth]
  · intro index hleft hright
    simp only [List.getElem_ofFn, canonicalDescriptionInput]

@[simp] theorem canonicalDescriptionInput_descriptionIndex
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (offset : Fin (rowWidth n bound)) :
    canonicalDescriptionInput circuit hsize
        (descriptionIndex row offset) =
      ((canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt))[offset.val]'(by
          rw [canonicalDescriptionRows_uniform circuit
            ((canonicalDescriptionRows bound circuit)[row.val]'(by
              rw [canonicalDescriptionRows_length circuit hsize]
              exact row.isLt))
            (List.getElem_mem (by
              rw [canonicalDescriptionRows_length circuit hsize]
              exact row.isLt))]
          exact offset.isLt) := by
  have haccess :=
    getElem_flatten_uniform
      (canonicalDescriptionRows bound circuit) (rowWidth n bound)
        row.val offset.val
        (canonicalDescriptionRows_uniform circuit)
        (by
          rw [canonicalDescriptionRows_length circuit hsize]
          exact row.isLt)
        offset.isLt
  simpa only [canonicalDescriptionInput,
    canonicalDescriptionRows_flatten, descriptionIndex] using haccess

theorem unaryEqualsExpr_eq_true_of_bits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (description : BitInput (descriptionWidth n bound))
    (hbits : ∀ offset : Fin limit,
      description (descriptionIndex row
        ⟨start + offset.val, by omega⟩) =
          decide (offset.val < value)) :
    (unaryEqualsExpr row start limit value hblock).eval
        description = true := by
  rw [unaryEqualsExpr_eval]
  apply List.all_eq_true.mpr
  intro item hitem
  rcases List.mem_ofFn.mp hitem with ⟨offset, rfl⟩
  rw [hbits offset]
  simp

/-- Converse to `unaryEqualsExpr_eq_true_of_bits`: a successful unary equality
guard fixes every bit in its block. -/
theorem unaryEqualsExpr_true_bits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (description : BitInput (descriptionWidth n bound))
    (htrue :
      (unaryEqualsExpr row start limit value hblock).eval
        description = true) :
    ∀ offset : Fin limit,
      description (descriptionIndex row
        ⟨start + offset.val, by omega⟩) =
          decide (offset.val < value) := by
  rw [unaryEqualsExpr_eval, List.all_eq_true] at htrue
  intro offset
  have hpoint := htrue
    (description (descriptionIndex row
        ⟨start + offset.val, by omega⟩) ==
      decide (offset.val < value))
    (List.mem_ofFn.mpr ⟨offset, rfl⟩)
  simpa using hpoint

theorem unaryEqualsExpr_eq_decide_of_bits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit actual candidate : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hactual : actual ≤ limit) (hcandidate : candidate ≤ limit)
    (description : BitInput (descriptionWidth n bound))
    (hbits : ∀ offset : Fin limit,
      description (descriptionIndex row
        ⟨start + offset.val, by omega⟩) =
          decide (offset.val < actual)) :
    (unaryEqualsExpr row start limit candidate hblock).eval
        description =
      decide (candidate = actual) := by
  rw [unaryEqualsExpr_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro hall
    by_contra hne
    rcases lt_or_gt_of_ne hne with hless | hgreater
    · let offset : Fin limit :=
        ⟨candidate, hless.trans_le hactual⟩
      have hpoint := hall
        (description (descriptionIndex row
            ⟨start + offset.val, by omega⟩) ==
          decide (offset.val < candidate))
        (List.mem_ofFn.mpr ⟨offset, rfl⟩)
      rw [hbits offset] at hpoint
      simp [offset, hless] at hpoint
    · let offset : Fin limit :=
        ⟨actual, hgreater.trans_le hcandidate⟩
      have hpoint := hall
        (description (descriptionIndex row
            ⟨start + offset.val, by omega⟩) ==
          decide (offset.val < candidate))
        (List.mem_ofFn.mpr ⟨offset, rfl⟩)
      rw [hbits offset] at hpoint
      simp [offset, hgreater] at hpoint
  · rintro rfl item hitem
    rcases List.mem_ofFn.mp hitem with ⟨offset, rfl⟩
    rw [hbits offset]
    simp

def encodedDescriptionRow (n bound tag first second : ℕ) :
    List Bool :=
  orderedNatBits 6 tag ++
    orderedNatBits (boundedCircuitFieldLimit n bound) first ++
      orderedNatBits (boundedCircuitFieldLimit n bound) second

@[simp] theorem encodedDescriptionRow_length
    (n bound tag first second : ℕ) :
    (encodedDescriptionRow n bound tag first second).length =
      rowWidth n bound := by
  simp [encodedDescriptionRow, rowWidth]
  omega

theorem tagEqualsExpr_canonicalRow
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (tag first second : ℕ)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound tag first second) :
    (tagEqualsExpr row tag).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  apply unaryEqualsExpr_eq_true_of_bits
  intro offset
  rw [canonicalDescriptionInput_descriptionIndex]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem]
  rw [hrow]
  rw [encodedDescriptionRow,
    List.getElem?_append_left (by
      simp only [List.length_append, orderedNatBits_length]
      omega)]
  rw [List.getElem?_append_left (by simp)]
  simp [orderedNatBits]

theorem firstFieldEqualsExpr_canonicalRow
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (tag first second : ℕ)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound tag first second) :
    (firstFieldEqualsExpr row first).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  apply unaryEqualsExpr_eq_true_of_bits
  intro offset
  rw [canonicalDescriptionInput_descriptionIndex]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem]
  rw [hrow]
  rw [encodedDescriptionRow,
    List.getElem?_append_left (by
      simp only [List.length_append, orderedNatBits_length]
      omega)]
  rw [List.getElem?_append_right (by simp)]
  simp [orderedNatBits]

theorem secondFieldEqualsExpr_canonicalRow
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (tag first second : ℕ)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound tag first second) :
    (secondFieldEqualsExpr row second).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  apply unaryEqualsExpr_eq_true_of_bits
  intro offset
  rw [canonicalDescriptionInput_descriptionIndex]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem]
  rw [hrow]
  rw [encodedDescriptionRow,
    List.getElem?_append_right (by simp)]
  simp [orderedNatBits]

theorem tagEqualsExpr_canonicalRow_eq
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (tag first second candidate : ℕ)
    (htag : tag ≤ 6) (hcandidate : candidate ≤ 6)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound tag first second) :
    (tagEqualsExpr row candidate).eval
        (canonicalDescriptionInput circuit hsize) =
      decide (candidate = tag) := by
  apply unaryEqualsExpr_eq_decide_of_bits
    row 0 6 tag candidate _ htag hcandidate
  intro offset
  rw [canonicalDescriptionInput_descriptionIndex]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, hrow, encodedDescriptionRow,
    List.getElem?_append_left (by
      simp only [List.length_append, orderedNatBits_length]
      omega),
    List.getElem?_append_left (by simp)]
  simp [orderedNatBits]

theorem firstFieldEqualsExpr_canonicalRow_eq
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (tag first second candidate : ℕ)
    (hfirst : first ≤ boundedCircuitFieldLimit n bound)
    (hcandidate : candidate ≤ boundedCircuitFieldLimit n bound)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound tag first second) :
    (firstFieldEqualsExpr row candidate).eval
        (canonicalDescriptionInput circuit hsize) =
      decide (candidate = first) := by
  apply unaryEqualsExpr_eq_decide_of_bits
    row 6 (boundedCircuitFieldLimit n bound) first candidate _
      hfirst hcandidate
  intro offset
  rw [canonicalDescriptionInput_descriptionIndex]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, hrow, encodedDescriptionRow,
    List.getElem?_append_left (by
      simp only [List.length_append, orderedNatBits_length]
      omega),
    List.getElem?_append_right (by simp)]
  simp [orderedNatBits]

theorem secondFieldEqualsExpr_canonicalRow_eq
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (tag first second candidate : ℕ)
    (hsecond : second ≤ boundedCircuitFieldLimit n bound)
    (hcandidate : candidate ≤ boundedCircuitFieldLimit n bound)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound tag first second) :
    (secondFieldEqualsExpr row candidate).eval
        (canonicalDescriptionInput circuit hsize) =
      decide (candidate = second) := by
  apply unaryEqualsExpr_eq_decide_of_bits
    row (6 + boundedCircuitFieldLimit n bound)
      (boundedCircuitFieldLimit n bound) second candidate _
      hsecond hcandidate
  intro offset
  rw [canonicalDescriptionInput_descriptionIndex]
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, hrow, encodedDescriptionRow,
    List.getElem?_append_right (by simp)]
  simp [orderedNatBits]

@[simp] theorem boundedNodeDescriptionBits_eq_encoded
    {n bound : ℕ} (node : BooleanNode n) :
    boundedNodeDescriptionBits bound node =
      match node with
      | .const value =>
          encodedDescriptionRow n bound 0 value.toNat 0
      | .input index =>
          encodedDescriptionRow n bound 1 index.val 0
      | .not child =>
          encodedDescriptionRow n bound 2 child 0
      | .and left right =>
          encodedDescriptionRow n bound 3 left right
      | .or left right =>
          encodedDescriptionRow n bound 4 left right := by
  cases node <;> rfl

@[simp] theorem boundedOutputDescriptionBits_eq_encoded
    (n bound output : ℕ) :
    boundedOutputDescriptionBits n bound output =
      encodedDescriptionRow n bound 5 output 0 := by
  rfl

@[simp] theorem boundedPaddingDescriptionBits_eq_encoded
    (n bound : ℕ) :
    boundedPaddingDescriptionBits n bound =
      encodedDescriptionRow n bound 6 0 0 := by
  rfl

@[simp] theorem canonicalDescriptionRows_get_node
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (index : Fin circuit.nodes.length) :
    (canonicalDescriptionRows bound circuit)[index.val]'(by
      simp only [canonicalDescriptionRows, List.length_append,
        List.length_map, List.length_singleton,
        List.length_replicate]
      omega) =
        boundedNodeDescriptionBits bound (circuit.nodes.get index) := by
  unfold canonicalDescriptionRows
  rw [List.getElem_append_left (by simp)]
  rw [List.getElem_append_left (by
    simpa only [List.length_map] using index.isLt)]
  simp [List.get_eq_getElem]

@[simp] theorem canonicalDescriptionRows_get_output
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (canonicalDescriptionRows bound circuit)[circuit.nodes.length]'(by
      rw [canonicalDescriptionRows_length circuit hsize]
      simpa only [BooleanCircuit.size] using
        Nat.lt_succ_of_le hsize) =
      boundedOutputDescriptionBits n bound circuit.output.val := by
  simp [canonicalDescriptionRows, BooleanCircuit.size]

@[simp] theorem canonicalDescriptionRows_get_padding
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound)
    (offset : Fin (bound - circuit.size)) :
    (canonicalDescriptionRows bound circuit)[
      circuit.nodes.length + 1 + offset.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        simp only [BooleanCircuit.size] at offset ⊢
        omega) =
      boundedPaddingDescriptionBits n bound := by
  unfold canonicalDescriptionRows
  rw [List.getElem_append_right (by simp)]
  simp [BooleanCircuit.size]

theorem firstFieldLessExpr_eq_true_of_equals
    {n bound : ℕ} (row : Fin (bound + 1))
    (value upper : ℕ) (hvalue : value < upper)
    (description : BitInput (descriptionWidth n bound))
    (hequals :
      (firstFieldEqualsExpr row value).eval description = true) :
    (firstFieldLessExpr row upper).eval description = true := by
  rw [firstFieldLessExpr, BoolExpr.eval_any, List.any_eq_true]
  exact
    ⟨firstFieldEqualsExpr row value,
      List.mem_map.mpr
        ⟨value, List.mem_range.mpr hvalue, rfl⟩,
      hequals⟩

theorem secondFieldLessExpr_eq_true_of_equals
    {n bound : ℕ} (row : Fin (bound + 1))
    (value upper : ℕ) (hvalue : value < upper)
    (description : BitInput (descriptionWidth n bound))
    (hequals :
      (secondFieldEqualsExpr row value).eval description = true) :
    (secondFieldLessExpr row upper).eval description = true := by
  rw [secondFieldLessExpr, BoolExpr.eval_any, List.any_eq_true]
  exact
    ⟨secondFieldEqualsExpr row value,
      List.mem_map.mpr
        ⟨value, List.mem_range.mpr hvalue, rfl⟩,
      hequals⟩

theorem selectFunctionValues_eq_get
    {n bound : ℕ}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (values : List (BoolFunction (descriptionWidth n bound)))
    (selected : Fin values.length)
    (description : BitInput (descriptionWidth n bound))
    (hfield : ∀ index : Fin values.length,
      (fieldEquals row index.val).eval description =
        decide (index.val = selected.val)) :
    selectFunctionValues fieldEquals row values description =
      (values.get selected) description := by
  apply Bool.eq_iff_iff.mpr
  rw [selectFunctionValues, List.any_eq_true]
  constructor
  · rintro ⟨entry, hentry, hcondition⟩
    rw [Bool.and_eq_true] at hcondition
    rcases hcondition with ⟨hguard, hvalue⟩
    have hentryInfo := List.mem_zipIdx' hentry
    let index : Fin values.length :=
      ⟨entry.2, hentryInfo.1⟩
    have hindex : index.val = selected.val := by
      have hguardExact := hfield index
      rw [hguardExact] at hguard
      simpa only [decide_eq_true_eq] using hguard
    have hvalueEq : entry.1 = values.get selected := by
      calc
        entry.1 = values.get index := by
          rw [List.get_eq_getElem]
          simpa only [index] using hentryInfo.2
        _ = values.get selected :=
          congrArg (fun item : Fin values.length =>
            values.get item) (Fin.ext hindex)
    rwa [hvalueEq] at hvalue
  · intro hvalue
    let entry :=
      (values.get selected, selected.val)
    refine ⟨entry, ?_, ?_⟩
    · apply List.mk_mem_zipIdx_iff_getElem?.mpr
      rw [List.getElem?_eq_getElem selected.isLt]
      rw [List.get_eq_getElem]
    · rw [Bool.and_eq_true]
      constructor
      · change
          (fieldEquals row selected.val).eval description = true
        rw [hfield selected]
        simp
      · exact hvalue

theorem constantAddressSelectionExpr_canonical_input
    {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (row : Fin (bound + 1)) (inputIndex : Fin n)
    (hrow :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound 1 inputIndex.val 0)
    (address : BitInput n) :
    (constantAddressSelectionExpr row address).eval
        (canonicalDescriptionInput circuit hsize) =
      address inputIndex := by
  apply Bool.eq_iff_iff.mpr
  rw [constantAddressSelectionExpr, BoolExpr.eval_any,
    List.any_eq_true]
  constructor
  · rintro ⟨expression, hexpression, heval⟩
    rcases List.mem_ofFn.mp hexpression with ⟨candidate, rfl⟩
    by_cases haddress : address candidate = true
    · rw [if_pos haddress] at heval
      have hfield :=
        firstFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 1 inputIndex.val 0 candidate.val
          (by
            simp [boundedCircuitFieldLimit]
            omega)
          (by
            simp [boundedCircuitFieldLimit]
            omega)
          hrow
      rw [hfield] at heval
      have hcandidate : candidate = inputIndex := by
        apply Fin.ext
        simpa only [decide_eq_true_eq] using heval
      simpa only [hcandidate] using haddress
    · rw [if_neg haddress] at heval
      cases heval
  · intro haddress
    refine
      ⟨if address inputIndex then
          firstFieldEqualsExpr row inputIndex.val
        else BoolExpr.const false,
        List.mem_ofFn.mpr ⟨inputIndex, rfl⟩, ?_⟩
    rw [if_pos haddress]
    have hfield :=
      firstFieldEqualsExpr_canonicalRow_eq
        circuit hsize row 1 inputIndex.val 0 inputIndex.val
        (by
          simp [boundedCircuitFieldLimit]
          omega)
        (by
          simp [boundedCircuitFieldLimit]
          omega)
        hrow
    simp only [hfield, decide_true]

theorem nodeRowExpr_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (index : Fin circuit.nodes.length) :
    (nodeRowExpr
      (n := n) (bound := bound)
      ⟨index.val, by
        have hnodes : circuit.nodes.length ≤ bound := by
          simpa only [BooleanCircuit.size] using hsize
        omega⟩).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  let row : Fin (bound + 1) :=
    ⟨index.val, by
      have hnodes : circuit.nodes.length ≤ bound := by
        simpa only [BooleanCircuit.size] using hsize
      omega⟩
  change
    (nodeRowExpr row).eval
      (canonicalDescriptionInput circuit hsize) = true
  have hrow :=
    canonicalDescriptionRows_get_node (bound := bound) circuit index
  have hwell := circuit.wellFormed index
  generalize hnode : circuit.nodes.get index = node at hrow hwell
  cases node with
  | const value =>
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 0 value.toNat 0 := by
        simpa [row] using hrow
      have htag :=
        tagEqualsExpr_canonicalRow circuit hsize row 0 value.toNat 0
          hencoded
      have hfirst :=
        firstFieldEqualsExpr_canonicalRow
          circuit hsize row 0 value.toNat 0 hencoded
      have hsecond :=
        secondFieldEqualsExpr_canonicalRow
          circuit hsize row 0 value.toNat 0 hencoded
      cases value with
      | false =>
          have hfirstZero :
              (firstFieldEqualsExpr row 0).eval
                  (canonicalDescriptionInput circuit hsize) = true := by
            simpa using hfirst
          simp [nodeRowExpr, htag, hfirstZero, hsecond]
      | true =>
          have hfirstOne :
              (firstFieldEqualsExpr row 1).eval
                  (canonicalDescriptionInput circuit hsize) = true := by
            simpa using hfirst
          simp [nodeRowExpr, htag, hfirstOne, hsecond]
  | input inputIndex =>
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 1 inputIndex.val 0 := by
        simpa [row] using hrow
      have htag :=
        tagEqualsExpr_canonicalRow
          circuit hsize row 1 inputIndex.val 0 hencoded
      have hfirst :=
        firstFieldEqualsExpr_canonicalRow
          circuit hsize row 1 inputIndex.val 0 hencoded
      have hless :=
        firstFieldLessExpr_eq_true_of_equals row inputIndex.val n
          inputIndex.isLt _ hfirst
      have hsecond :=
        secondFieldEqualsExpr_canonicalRow
          circuit hsize row 1 inputIndex.val 0 hencoded
      simp [nodeRowExpr, htag, hless, hsecond]
  | not child =>
      have hchild : child < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 2 child 0 := by
        simpa [row] using hrow
      have htag :=
        tagEqualsExpr_canonicalRow
          circuit hsize row 2 child 0 hencoded
      have hfirst :=
        firstFieldEqualsExpr_canonicalRow
          circuit hsize row 2 child 0 hencoded
      have hless :=
        firstFieldLessExpr_eq_true_of_equals row child row.val
          (by simpa [row] using hchild) _ hfirst
      have hsecond :=
        secondFieldEqualsExpr_canonicalRow
          circuit hsize row 2 child 0 hencoded
      simp [nodeRowExpr, htag, hless, hsecond]
  | and left right =>
      have hleft : left < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.1
      have hright : right < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.2
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 3 left right := by
        simpa [row] using hrow
      have htag :=
        tagEqualsExpr_canonicalRow
          circuit hsize row 3 left right hencoded
      have hfirst :=
        firstFieldEqualsExpr_canonicalRow
          circuit hsize row 3 left right hencoded
      have hfirstLess :=
        firstFieldLessExpr_eq_true_of_equals row left row.val
          (by simpa [row] using hleft) _ hfirst
      have hsecond :=
        secondFieldEqualsExpr_canonicalRow
          circuit hsize row 3 left right hencoded
      have hsecondLess :=
        secondFieldLessExpr_eq_true_of_equals row right row.val
          (by simpa [row] using hright) _ hsecond
      simp [nodeRowExpr, htag, hfirstLess, hsecondLess]
  | or left right =>
      have hleft : left < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.1
      have hright : right < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.2
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 4 left right := by
        simpa [row] using hrow
      have htag :=
        tagEqualsExpr_canonicalRow
          circuit hsize row 4 left right hencoded
      have hfirst :=
        firstFieldEqualsExpr_canonicalRow
          circuit hsize row 4 left right hencoded
      have hfirstLess :=
        firstFieldLessExpr_eq_true_of_equals row left row.val
          (by simpa [row] using hleft) _ hfirst
      have hsecond :=
        secondFieldEqualsExpr_canonicalRow
          circuit hsize row 4 left right hencoded
      have hsecondLess :=
        secondFieldLessExpr_eq_true_of_equals row right row.val
          (by simpa [row] using hright) _ hsecond
      simp [nodeRowExpr, htag, hfirstLess, hsecondLess]

theorem outputRowExpr_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    (outputRowExpr
      (n := n) (bound := bound)
      ⟨circuit.nodes.length, by
        simpa only [BooleanCircuit.size] using
          Nat.lt_succ_of_le hsize⟩).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  let row : Fin (bound + 1) :=
    ⟨circuit.nodes.length, by
      simpa only [BooleanCircuit.size] using
        Nat.lt_succ_of_le hsize⟩
  change
    (outputRowExpr row).eval
      (canonicalDescriptionInput circuit hsize) = true
  have hrow :=
    canonicalDescriptionRows_get_output circuit hsize
  have hencoded :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound 5 circuit.output.val 0 := by
    simpa [row] using hrow
  have htag :=
    tagEqualsExpr_canonicalRow
      circuit hsize row 5 circuit.output.val 0 hencoded
  have hfirst :=
    firstFieldEqualsExpr_canonicalRow
      circuit hsize row 5 circuit.output.val 0 hencoded
  have hless :=
    firstFieldLessExpr_eq_true_of_equals
      row circuit.output.val row.val
      (by simp [row, circuit.output.isLt]) _ hfirst
  have hsecond :=
    secondFieldEqualsExpr_canonicalRow
      circuit hsize row 5 circuit.output.val 0 hencoded
  simp [outputRowExpr, htag, hless, hsecond]

theorem paddingRowExpr_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (offset : Fin (bound - circuit.size)) :
    (paddingRowExpr
      (n := n) (bound := bound)
      ⟨circuit.nodes.length + 1 + offset.val, by
        simp only [BooleanCircuit.size] at offset ⊢
        have hnodes : circuit.nodes.length ≤ bound := by
          simpa only [BooleanCircuit.size] using hsize
        omega⟩).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  let row : Fin (bound + 1) :=
    ⟨circuit.nodes.length + 1 + offset.val, by
      simp only [BooleanCircuit.size] at offset ⊢
      have hnodes : circuit.nodes.length ≤ bound := by
        simpa only [BooleanCircuit.size] using hsize
      omega⟩
  change
    (paddingRowExpr row).eval
      (canonicalDescriptionInput circuit hsize) = true
  have hrow :=
    canonicalDescriptionRows_get_padding circuit hsize offset
  have hencoded :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound 6 0 0 := by
    simpa [row] using hrow
  have htag :=
    tagEqualsExpr_canonicalRow circuit hsize row 6 0 0 hencoded
  have hfirst :=
    firstFieldEqualsExpr_canonicalRow
      circuit hsize row 6 0 0 hencoded
  have hsecond :=
    secondFieldEqualsExpr_canonicalRow
      circuit hsize row 6 0 0 hencoded
  simp [paddingRowExpr, htag, hfirst, hsecond]

def circuitCountIndex {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    Fin bound :=
  ⟨circuit.nodes.length - 1, by
    have hpositive : 0 < circuit.nodes.length :=
      Nat.zero_lt_of_lt circuit.output.isLt
    have hnodes : circuit.nodes.length ≤ bound := by
      simpa only [BooleanCircuit.size] using hsize
    exact
      (Nat.sub_lt hpositive (by omega)).trans_le hnodes⟩

@[simp] theorem circuitCountIndex_succ {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    (circuitCountIndex circuit hsize).val + 1 =
      circuit.nodes.length := by
  unfold circuitCountIndex
  have hpositive : 0 < circuit.nodes.length :=
    Nat.zero_lt_of_lt circuit.output.isLt
  exact Nat.sub_add_cancel (by omega)

theorem fixedCountGrammarExpr_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    (fixedCountGrammarExpr (circuitCountIndex circuit hsize)).eval
        (canonicalDescriptionInput circuit hsize) = true := by
  let count := circuitCountIndex circuit hsize
  rw [fixedCountGrammarExpr, BoolExpr.eval_all,
    List.all_append, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro expression hexpression
    rw [countNodeRows] at hexpression
    rcases List.mem_ofFn.mp hexpression with ⟨nodeIndex, rfl⟩
    let actualIndex : Fin circuit.nodes.length :=
      ⟨nodeIndex.val, by
        rw [← circuitCountIndex_succ circuit hsize]
        exact nodeIndex.isLt⟩
    convert nodeRowExpr_canonical circuit hsize actualIndex using 1
  · rw [List.all_cons, Bool.and_eq_true]
    constructor
    · let outputRow : Fin (bound + 1) :=
        ⟨(circuitCountIndex circuit hsize).val + 1, by omega⟩
      change
        (outputRowExpr outputRow).eval
          (canonicalDescriptionInput circuit hsize) = true
      have houtputRow :
          outputRow =
            ⟨circuit.nodes.length, by
              simpa only [BooleanCircuit.size] using
                Nat.lt_succ_of_le hsize⟩ := by
        apply Fin.ext
        exact circuitCountIndex_succ circuit hsize
      rw [houtputRow]
      exact outputRowExpr_canonical circuit hsize
    · apply List.all_eq_true.mpr
      intro expression hexpression
      rw [countPaddingRows] at hexpression
      rcases List.mem_ofFn.mp hexpression with
        ⟨paddingOffset, rfl⟩
      have hremaining :
          bound - ((circuitCountIndex circuit hsize).val + 1) =
            bound - circuit.size := by
        rw [circuitCountIndex_succ]
        rfl
      let actualOffset : Fin (bound - circuit.size) :=
        Fin.cast hremaining paddingOffset
      let paddingRow : Fin (bound + 1) :=
        ⟨(circuitCountIndex circuit hsize).val + 2 +
            paddingOffset.val, by omega⟩
      change
        (paddingRowExpr paddingRow).eval
          (canonicalDescriptionInput circuit hsize) = true
      have hpaddingRow :
          paddingRow =
            ⟨circuit.nodes.length + 1 + actualOffset.val, by
              simp only [BooleanCircuit.size] at actualOffset ⊢
              have hnodes : circuit.nodes.length ≤ bound := by
                simpa only [BooleanCircuit.size] using hsize
              omega⟩ := by
        apply Fin.ext
        dsimp only [paddingRow, actualOffset]
        rw [Fin.val_cast]
        have hcount :=
          circuitCountIndex_succ circuit hsize
        omega
      rw [hpaddingRow]
      exact paddingRowExpr_canonical circuit hsize actualOffset

/-- Looking up an evaluated function after converting the evaluation list to
an array agrees with evaluating the corresponding source function. -/
theorem mappedFunctionArray_getD {width : ℕ}
    (values : List (BoolFunction width)) (description : BitInput width)
    (index : ℕ) (hindex : index < values.length) :
    ((values.map fun value => value description).toArray[index]?).getD false =
      (values.get ⟨index, hindex⟩) description := by
  rw [Array.getElem?_eq_getElem (by simpa)]
  simp [List.get_eq_getElem]

/-- On a canonical description, one row of the universal evaluator performs
exactly the operation of the corresponding source-circuit node.  The theorem
is parametric in the already-compiled prefix, which is the sharing invariant
needed by the recursive evaluator proof below. -/
theorem universalNodeValue_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (index : Fin circuit.nodes.length) (address : BitInput n)
    (priorValues :
      List (BoolFunction (descriptionWidth n bound)))
    (hlength : priorValues.length = index.val) :
    universalNodeValue
        (n := n) (bound := bound)
        ⟨index.val, by
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          omega⟩
        address priorValues (canonicalDescriptionInput circuit hsize) =
      (circuit.nodes.get index).eval address
        ((priorValues.map fun value =>
          value (canonicalDescriptionInput circuit hsize)).toArray) := by
  let row : Fin (bound + 1) :=
    ⟨index.val, by
      have hnodes : circuit.nodes.length ≤ bound := by
        simpa only [BooleanCircuit.size] using hsize
      omega⟩
  change
    universalNodeValue row address priorValues
        (canonicalDescriptionInput circuit hsize) =
      (circuit.nodes.get index).eval address
        ((priorValues.map fun value =>
          value (canonicalDescriptionInput circuit hsize)).toArray)
  have hrow :=
    canonicalDescriptionRows_get_node (bound := bound) circuit index
  have hwell := circuit.wellFormed index
  generalize hnode : circuit.nodes.get index = node at hrow hwell ⊢
  cases node with
  | const value =>
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 0 value.toNat 0 := by
        simpa [row] using hrow
      have htag0 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 0 value.toNat 0 0 (by omega) (by omega)
          hencoded
      have htag1 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 0 value.toNat 0 1 (by omega) (by omega)
          hencoded
      have htag2 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 0 value.toNat 0 2 (by omega) (by omega)
          hencoded
      have htag3 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 0 value.toNat 0 3 (by omega) (by omega)
          hencoded
      have htag4 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 0 value.toNat 0 4 (by omega) (by omega)
          hencoded
      have hvalue :=
        firstFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 0 value.toNat 0 1
          (by
            cases value <;> simp [boundedCircuitFieldLimit])
          (by simp [boundedCircuitFieldLimit])
          hencoded
      cases value <;>
        simp [universalNodeValue, BooleanNode.eval, htag0, htag1,
          htag2, htag3, htag4, hvalue]
  | input inputIndex =>
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 1 inputIndex.val 0 := by
        simpa [row] using hrow
      have htag0 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 1 inputIndex.val 0 0 (by omega) (by omega)
          hencoded
      have htag1 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 1 inputIndex.val 0 1 (by omega) (by omega)
          hencoded
      have htag2 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 1 inputIndex.val 0 2 (by omega) (by omega)
          hencoded
      have htag3 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 1 inputIndex.val 0 3 (by omega) (by omega)
          hencoded
      have htag4 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 1 inputIndex.val 0 4 (by omega) (by omega)
          hencoded
      have hinput :=
        constantAddressSelectionExpr_canonical_input
          circuit hsize row inputIndex hencoded address
      simp [universalNodeValue, BooleanNode.eval, htag0, htag1,
        htag2, htag3, htag4, hinput]
  | not child =>
      have hchild : child < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 2 child 0 := by
        simpa [row] using hrow
      have htag0 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 2 child 0 0 (by omega) (by omega) hencoded
      have htag1 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 2 child 0 1 (by omega) (by omega) hencoded
      have htag2 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 2 child 0 2 (by omega) (by omega) hencoded
      have htag3 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 2 child 0 3 (by omega) (by omega) hencoded
      have htag4 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 2 child 0 4 (by omega) (by omega) hencoded
      let selected : Fin priorValues.length :=
        ⟨child, by simpa only [hlength] using hchild⟩
      have hselection :
          selectFunctionValues firstFieldEqualsExpr row priorValues
              (canonicalDescriptionInput circuit hsize) =
            (priorValues.get selected)
              (canonicalDescriptionInput circuit hsize) := by
        apply selectFunctionValues_eq_get
        intro candidate
        apply firstFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 2 child 0 candidate.val
        · simp [boundedCircuitFieldLimit]
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          omega
        · have hc : candidate.val < index.val := by
            simpa only [hlength] using candidate.isLt
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          simp only [boundedCircuitFieldLimit]
          omega
        · exact hencoded
      have hlookup :
          ((priorValues.map fun value =>
            value (canonicalDescriptionInput circuit hsize)).toArray[child]?).getD
              false =
            (priorValues.get selected)
              (canonicalDescriptionInput circuit hsize) := by
        exact mappedFunctionArray_getD priorValues
          (canonicalDescriptionInput circuit hsize) child
          (by simpa only [hlength] using hchild)
      rw [BooleanNode.eval, hlookup]
      simp [universalNodeValue, htag0, htag1, htag2, htag3, htag4,
        hselection]
  | and left right =>
      have hleft : left < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.1
      have hright : right < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.2
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 3 left right := by
        simpa [row] using hrow
      have htag0 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right 0 (by omega) (by omega) hencoded
      have htag1 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right 1 (by omega) (by omega) hencoded
      have htag2 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right 2 (by omega) (by omega) hencoded
      have htag3 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right 3 (by omega) (by omega) hencoded
      have htag4 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right 4 (by omega) (by omega) hencoded
      let leftIndex : Fin priorValues.length :=
        ⟨left, by simpa only [hlength] using hleft⟩
      let rightIndex : Fin priorValues.length :=
        ⟨right, by simpa only [hlength] using hright⟩
      have hleftSelection :
          selectFunctionValues firstFieldEqualsExpr row priorValues
              (canonicalDescriptionInput circuit hsize) =
            (priorValues.get leftIndex)
              (canonicalDescriptionInput circuit hsize) := by
        apply selectFunctionValues_eq_get
        intro candidate
        apply firstFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right candidate.val
        · simp [boundedCircuitFieldLimit]
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          omega
        · have hc : candidate.val < index.val := by
            simpa only [hlength] using candidate.isLt
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          simp only [boundedCircuitFieldLimit]
          omega
        · exact hencoded
      have hrightSelection :
          selectFunctionValues secondFieldEqualsExpr row priorValues
              (canonicalDescriptionInput circuit hsize) =
            (priorValues.get rightIndex)
              (canonicalDescriptionInput circuit hsize) := by
        apply selectFunctionValues_eq_get
        intro candidate
        apply secondFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 3 left right candidate.val
        · simp [boundedCircuitFieldLimit]
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          omega
        · have hc : candidate.val < index.val := by
            simpa only [hlength] using candidate.isLt
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          simp only [boundedCircuitFieldLimit]
          omega
        · exact hencoded
      have hleftLookup :=
        mappedFunctionArray_getD priorValues
          (canonicalDescriptionInput circuit hsize) left
          (by simpa only [hlength] using hleft)
      have hrightLookup :=
        mappedFunctionArray_getD priorValues
          (canonicalDescriptionInput circuit hsize) right
          (by simpa only [hlength] using hright)
      rw [BooleanNode.eval, hleftLookup, hrightLookup]
      simp [universalNodeValue, htag0, htag1, htag2, htag3, htag4,
        hleftSelection, hrightSelection]
      rfl
  | or left right =>
      have hleft : left < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.1
      have hright : right < index.val := by
        simpa [BooleanNode.WellFormedAt] using hwell.2
      have hencoded :
          (canonicalDescriptionRows bound circuit)[row.val]'(by
            rw [canonicalDescriptionRows_length circuit hsize]
            exact row.isLt) =
            encodedDescriptionRow n bound 4 left right := by
        simpa [row] using hrow
      have htag0 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right 0 (by omega) (by omega) hencoded
      have htag1 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right 1 (by omega) (by omega) hencoded
      have htag2 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right 2 (by omega) (by omega) hencoded
      have htag3 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right 3 (by omega) (by omega) hencoded
      have htag4 :=
        tagEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right 4 (by omega) (by omega) hencoded
      let leftIndex : Fin priorValues.length :=
        ⟨left, by simpa only [hlength] using hleft⟩
      let rightIndex : Fin priorValues.length :=
        ⟨right, by simpa only [hlength] using hright⟩
      have hleftSelection :
          selectFunctionValues firstFieldEqualsExpr row priorValues
              (canonicalDescriptionInput circuit hsize) =
            (priorValues.get leftIndex)
              (canonicalDescriptionInput circuit hsize) := by
        apply selectFunctionValues_eq_get
        intro candidate
        apply firstFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right candidate.val
        · simp [boundedCircuitFieldLimit]
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          omega
        · have hc : candidate.val < index.val := by
            simpa only [hlength] using candidate.isLt
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          simp only [boundedCircuitFieldLimit]
          omega
        · exact hencoded
      have hrightSelection :
          selectFunctionValues secondFieldEqualsExpr row priorValues
              (canonicalDescriptionInput circuit hsize) =
            (priorValues.get rightIndex)
              (canonicalDescriptionInput circuit hsize) := by
        apply selectFunctionValues_eq_get
        intro candidate
        apply secondFieldEqualsExpr_canonicalRow_eq
          circuit hsize row 4 left right candidate.val
        · simp [boundedCircuitFieldLimit]
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          omega
        · have hc : candidate.val < index.val := by
            simpa only [hlength] using candidate.isLt
          have hnodes : circuit.nodes.length ≤ bound := by
            simpa only [BooleanCircuit.size] using hsize
          simp only [boundedCircuitFieldLimit]
          omega
        · exact hencoded
      have hleftLookup :=
        mappedFunctionArray_getD priorValues
          (canonicalDescriptionInput circuit hsize) left
          (by simpa only [hlength] using hleft)
      have hrightLookup :=
        mappedFunctionArray_getD priorValues
          (canonicalDescriptionInput circuit hsize) right
          (by simpa only [hlength] using hright)
      rw [BooleanNode.eval, hleftLookup, hrightLookup]
      simp [universalNodeValue, htag0, htag1, htag2, htag3, htag4,
        hleftSelection, hrightSelection]
      rfl

/-- Reference evaluation of a source-circuit prefix, expressed with lists so
that it can be compared directly with the function list maintained by the
universal evaluator. -/
def sourcePrefixValues {n : ℕ} (circuit : BooleanCircuit n)
    (address : BitInput n) (count : ℕ) : List Bool :=
  (circuit.nodes.take count).foldl
    (fun prior node =>
      prior ++ [node.eval address prior.toArray]) []

/-- Evaluating all universal node functions generated for a prefix of a
canonical description yields exactly the source circuit's prefix values. -/
theorem universalNodeValues_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (address : BitInput n) (count : ℕ)
    (hbound : count ≤ bound) (hcircuit : count ≤ circuit.nodes.length) :
    (universalNodeValues
        (n := n) (bound := bound) address count hbound).map
        (fun value => value (canonicalDescriptionInput circuit hsize)) =
      sourcePrefixValues circuit address count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      have hcountCircuit : count < circuit.nodes.length := by
        omega
      have hcountBound : count ≤ bound := by
        omega
      let index : Fin circuit.nodes.length :=
        ⟨count, hcountCircuit⟩
      have hnode :=
        universalNodeValue_canonical circuit hsize index address
          (universalNodeValues address count hcountBound)
          (universalNodeValues_length address count hcountBound)
      simp only [universalNodeValues, List.map_append, List.map_singleton]
      rw [hnode]
      rw [inductionHypothesis hcountBound (by omega)]
      simp only [sourcePrefixValues,
        List.take_succ_eq_append_getElem hcountCircuit,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl

/-- List-based prefix evaluation is definitionally the same fold as the
repository's array-based circuit semantics. -/
theorem sourceNodeFold_toArray {n : ℕ} (address : BitInput n)
    (nodes : List (BooleanNode n)) (prior : List Bool) :
    (nodes.foldl
        (fun values node =>
          values ++ [node.eval address values.toArray]) prior).toArray =
      nodes.foldl
        (fun values node =>
          values.push (node.eval address values)) prior.toArray := by
  induction nodes generalizing prior with
  | nil =>
      rfl
  | cons node rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      simp

@[simp] theorem sourcePrefixValues_full_toArray {n : ℕ}
    (circuit : BooleanCircuit n) (address : BitInput n) :
    (sourcePrefixValues circuit address circuit.nodes.length).toArray =
      circuit.values address := by
  rw [sourcePrefixValues, List.take_length]
  exact sourceNodeFold_toArray address circuit.nodes []

/-- The complete universal evaluator agrees extensionally with the described
source circuit on every address. -/
theorem universalOutputValue_canonical {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound)
    (address : BitInput n) :
    universalOutputValue
        (n := n) (bound := bound) address circuit.nodes.length
        (by simpa only [BooleanCircuit.size] using hsize)
        (canonicalDescriptionInput circuit hsize) =
      circuit.eval address := by
  let hbound : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  let values :=
    universalNodeValues
      (n := n) (bound := bound) address circuit.nodes.length hbound
  let row : Fin (bound + 1) :=
    ⟨circuit.nodes.length, by omega⟩
  let selected : Fin values.length :=
    ⟨circuit.output.val, by
      simpa only [values, universalNodeValues_length] using
        circuit.output.isLt⟩
  change
    selectFunctionValues firstFieldEqualsExpr row values
        (canonicalDescriptionInput circuit hsize) =
      circuit.eval address
  have hrow :=
    canonicalDescriptionRows_get_output circuit hsize
  have hencoded :
      (canonicalDescriptionRows bound circuit)[row.val]'(by
        rw [canonicalDescriptionRows_length circuit hsize]
        exact row.isLt) =
        encodedDescriptionRow n bound 5 circuit.output.val 0 := by
    simpa [row] using hrow
  have hselection :
      selectFunctionValues firstFieldEqualsExpr row values
          (canonicalDescriptionInput circuit hsize) =
        (values.get selected)
          (canonicalDescriptionInput circuit hsize) := by
    apply selectFunctionValues_eq_get
    intro candidate
    apply firstFieldEqualsExpr_canonicalRow_eq
      circuit hsize row 5 circuit.output.val 0 candidate.val
    · simp [boundedCircuitFieldLimit]
      have hnodes : circuit.nodes.length ≤ bound := by
        simpa only [BooleanCircuit.size] using hsize
      omega
    · have hc : candidate.val < circuit.nodes.length := by
        simpa only [values, universalNodeValues_length] using
          candidate.isLt
      simp only [boundedCircuitFieldLimit]
      omega
    · exact hencoded
  rw [hselection]
  have hlookup :=
    mappedFunctionArray_getD values
      (canonicalDescriptionInput circuit hsize) circuit.output.val
      (by
        simpa only [values, universalNodeValues_length] using
          circuit.output.isLt)
  rw [← hlookup]
  have hvalues :=
    universalNodeValues_canonical circuit hsize address
      circuit.nodes.length hbound (by omega)
  have harrayValues := congrArg List.toArray hvalues
  rw [harrayValues]
  rw [sourcePrefixValues_full_toArray]
  rfl

/-- Query assignment induced by a canonical description is exactly the
assignment obtained by invoking the source circuit at each projected address. -/
theorem describedQueryAssignment_canonical
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hsize : circuit.size ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) :
    describedQueryAssignment pcp input circuit.nodes.length
        (by simpa only [BooleanCircuit.size] using hsize)
        randomness (canonicalDescriptionInput circuit hsize) =
      fun query =>
        circuit.eval (projectedInput pcp input randomness query) := by
  funext query
  exact universalOutputValue_canonical circuit hsize
    (projectedInput pcp input randomness query)

/-- One structurally evaluated verifier row is the repository's native oracle
acceptance predicate when the description is canonical. -/
theorem verifierRowValue_canonical
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hsize : circuit.size ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) :
    verifierRowValue pcp input circuit.nodes.length
        (by simpa only [BooleanCircuit.size] using hsize)
        randomness (canonicalDescriptionInput circuit hsize) =
      acceptsOracleCircuit pcp input circuit randomness := by
  unfold verifierRowValue acceptsOracleCircuit
  rw [describedQueryAssignment_canonical]

/-- A universally accepting bounded circuit makes its exact node-count branch
of the structural verifier true. -/
theorem fixedCountValue_canonical_of_accepts
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hsize : circuit.size ≤ bound)
    (haccepts : ∀ randomness,
      acceptsOracleCircuit pcp input circuit randomness = true) :
    fixedCountValue pcp input (circuitCountIndex circuit hsize)
        (canonicalDescriptionInput circuit hsize) = true := by
  rw [fixedCountValue, Bool.and_eq_true]
  constructor
  · exact fixedCountGrammarExpr_canonical circuit hsize
  · unfold verifierRowsValue
    apply List.all_eq_true.mpr
    intro randomness _hrandomness
    have hrow :=
      verifierRowValue_canonical pcp input circuit hsize randomness
    have hcount := circuitCountIndex_succ circuit hsize
    simpa only [hcount] using hrow.trans (haccepts randomness)

/-- Completeness of the structural predicate: every universally accepting
bounded source circuit contributes its canonical description as a satisfying
assignment. -/
theorem boundedOraclePredicate_canonical_of_accepts
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hsize : circuit.size ≤ bound)
    (haccepts : ∀ randomness,
      acceptsOracleCircuit pcp input circuit randomness = true) :
    boundedOraclePredicate pcp input bound
        (canonicalDescriptionInput circuit hsize) = true := by
  rw [boundedOraclePredicate, countCasesValue, List.any_eq_true]
  refine
    ⟨circuitCountIndex circuit hsize, ?_,
      fixedCountValue_canonical_of_accepts
        pcp input circuit hsize haccepts⟩
  exact List.mem_ofFn.mpr
    ⟨circuitCountIndex circuit hsize, rfl⟩

/-! ## Sound decoding of arbitrary satisfying descriptions -/

def boundedNodeTag {n index : ℕ} :
    BoundedBooleanNode n index → ℕ
  | .const _ => 0
  | .input _ => 1
  | .not _ => 2
  | .and _ _ => 3
  | .or _ _ => 4

def boundedNodeFirst {n index : ℕ} :
    BoundedBooleanNode n index → ℕ
  | .const value => value.toNat
  | .input inputIndex => inputIndex.val
  | .not child => child.val
  | .and left _ => left.val
  | .or left _ => left.val

def boundedNodeSecond {n index : ℕ} :
    BoundedBooleanNode n index → ℕ
  | .const _ => 0
  | .input _ => 0
  | .not _ => 0
  | .and _ right => right.val
  | .or _ right => right.val

@[simp] theorem boundedNodeDescriptionBits_bounded_eq_encoded
    {n bound index : ℕ} (node : BoundedBooleanNode n index) :
    boundedNodeDescriptionBits bound node.toNode =
      encodedDescriptionRow n bound
        (boundedNodeTag node) (boundedNodeFirst node)
        (boundedNodeSecond node) := by
  cases node <;> rfl

/-- Evidence that one raw description row is the exact unary encoding of
three structural fields. -/
structure RowMatchesEncoded {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1)) (tag first second : ℕ) : Prop where
  tagTrue :
    (tagEqualsExpr row tag).eval description = true
  firstTrue :
    (firstFieldEqualsExpr row first).eval description = true
  secondTrue :
    (secondFieldEqualsExpr row second).eval description = true

structure DecodedNodeRow {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1)) where
  node : BoundedBooleanNode n row.val
  encoding : RowMatchesEncoded description row
    (boundedNodeTag node) (boundedNodeFirst node)
    (boundedNodeSecond node)

private theorem firstFieldLessExpr_true_exists
    {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1)) (upper : ℕ)
    (htrue : (firstFieldLessExpr row upper).eval description = true) :
    ∃ value, value < upper ∧
      (firstFieldEqualsExpr row value).eval description = true := by
  rw [firstFieldLessExpr, BoolExpr.eval_any, List.any_eq_true] at htrue
  rcases htrue with ⟨expression, hexpression, heval⟩
  rcases List.mem_map.mp hexpression with
    ⟨value, hvalue, rfl⟩
  exact ⟨value, List.mem_range.mp hvalue, heval⟩

private theorem secondFieldLessExpr_true_exists
    {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1)) (upper : ℕ)
    (htrue : (secondFieldLessExpr row upper).eval description = true) :
    ∃ value, value < upper ∧
      (secondFieldEqualsExpr row value).eval description = true := by
  rw [secondFieldLessExpr, BoolExpr.eval_any, List.any_eq_true] at htrue
  rcases htrue with ⟨expression, hexpression, heval⟩
  rcases List.mem_map.mp hexpression with
    ⟨value, hvalue, rfl⟩
  exact ⟨value, List.mem_range.mp hvalue, heval⟩

/-- The node grammar is a total typed decoder: every successful node row
produces one topologically well-formed bounded node and its exact row fields. -/
theorem nodeRowExpr_true_decodes {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (htrue : (nodeRowExpr row).eval description = true) :
    Nonempty (DecodedNodeRow description row) := by
  rw [nodeRowExpr, BoolExpr.eval_any, List.any_eq_true] at htrue
  rcases htrue with ⟨expression, hexpression, heval⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hexpression
  rcases hexpression with
      rfl | rfl | rfl | rfl | rfl
  · rw [BoolExpr.eval_all, List.all_eq_true] at heval
    have htag := heval (tagEqualsExpr row 0) (by simp)
    have hconstant := heval
      (BoolExpr.any
        [firstFieldEqualsExpr row 0, firstFieldEqualsExpr row 1])
      (by simp)
    have hsecond := heval (secondFieldEqualsExpr row 0) (by simp)
    rw [BoolExpr.eval_any, List.any_eq_true] at hconstant
    rcases hconstant with ⟨candidate, hcandidate, hcandTrue⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact ⟨
        { node := .const false
          encoding := ⟨htag, hcandTrue, hsecond⟩ }⟩
    · exact ⟨
        { node := .const true
          encoding := ⟨htag, hcandTrue, hsecond⟩ }⟩
  · rw [BoolExpr.eval_all, List.all_eq_true] at heval
    have htag := heval (tagEqualsExpr row 1) (by simp)
    have hfirstLess := heval (firstFieldLessExpr row n) (by simp)
    have hsecond := heval (secondFieldEqualsExpr row 0) (by simp)
    rcases firstFieldLessExpr_true_exists
        description row n hfirstLess with
      ⟨inputIndex, hinputIndex, hfirst⟩
    exact ⟨
      { node := .input ⟨inputIndex, hinputIndex⟩
        encoding := ⟨htag, hfirst, hsecond⟩ }⟩
  · rw [BoolExpr.eval_all, List.all_eq_true] at heval
    have htag := heval (tagEqualsExpr row 2) (by simp)
    have hfirstLess :=
      heval (firstFieldLessExpr row row.val) (by simp)
    have hsecond := heval (secondFieldEqualsExpr row 0) (by simp)
    rcases firstFieldLessExpr_true_exists
        description row row.val hfirstLess with
      ⟨child, hchild, hfirst⟩
    exact ⟨
      { node := .not ⟨child, hchild⟩
        encoding := ⟨htag, hfirst, hsecond⟩ }⟩
  · rw [BoolExpr.eval_all, List.all_eq_true] at heval
    have htag := heval (tagEqualsExpr row 3) (by simp)
    have hfirstLess :=
      heval (firstFieldLessExpr row row.val) (by simp)
    have hsecondLess :=
      heval (secondFieldLessExpr row row.val) (by simp)
    rcases firstFieldLessExpr_true_exists
        description row row.val hfirstLess with
      ⟨left, hleft, hfirst⟩
    rcases secondFieldLessExpr_true_exists
        description row row.val hsecondLess with
      ⟨right, hright, hsecond⟩
    exact ⟨
      { node := .and ⟨left, hleft⟩ ⟨right, hright⟩
        encoding := ⟨htag, hfirst, hsecond⟩ }⟩
  · rw [BoolExpr.eval_all, List.all_eq_true] at heval
    have htag := heval (tagEqualsExpr row 4) (by simp)
    have hfirstLess :=
      heval (firstFieldLessExpr row row.val) (by simp)
    have hsecondLess :=
      heval (secondFieldLessExpr row row.val) (by simp)
    rcases firstFieldLessExpr_true_exists
        description row row.val hfirstLess with
      ⟨left, hleft, hfirst⟩
    rcases secondFieldLessExpr_true_exists
        description row row.val hsecondLess with
      ⟨right, hright, hsecond⟩
    exact ⟨
      { node := .or ⟨left, hleft⟩ ⟨right, hright⟩
        encoding := ⟨htag, hfirst, hsecond⟩ }⟩

structure DecodedOutputRow {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1)) where
  output : Fin row.val
  encoding : RowMatchesEncoded description row 5 output.val 0

theorem outputRowExpr_true_decodes {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (htrue : (outputRowExpr row).eval description = true) :
    Nonempty (DecodedOutputRow description row) := by
  rw [outputRowExpr, BoolExpr.eval_all, List.all_eq_true] at htrue
  have htag := htrue (tagEqualsExpr row 5) (by simp)
  have hfirstLess :=
    htrue (firstFieldLessExpr row row.val) (by simp)
  have hsecond := htrue (secondFieldEqualsExpr row 0) (by simp)
  rcases firstFieldLessExpr_true_exists
      description row row.val hfirstLess with
    ⟨output, houtput, hfirst⟩
  exact ⟨
    { output := ⟨output, houtput⟩
      encoding := ⟨htag, hfirst, hsecond⟩ }⟩

theorem paddingRowExpr_true_encoding {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (htrue : (paddingRowExpr row).eval description = true) :
    RowMatchesEncoded description row 6 0 0 := by
  rw [paddingRowExpr, BoolExpr.eval_all, List.all_eq_true] at htrue
  exact
    ⟨htrue (tagEqualsExpr row 6) (by simp),
      htrue (firstFieldEqualsExpr row 0) (by simp),
      htrue (secondFieldEqualsExpr row 0) (by simp)⟩

/-- A decoded fixed-count branch retains row evidence alongside the typed
nodes.  Keeping these dependent witnesses together prevents a second,
potentially inconsistent decoding path. -/
structure DecodedFixedCount {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (count : Fin bound) where
  nodes : (index : Fin (count.val + 1)) →
    DecodedNodeRow description
      ⟨index.val, by
        have hcount := count.isLt
        have hindex := index.isLt
        omega⟩
  output : DecodedOutputRow description
    ⟨count.val + 1, by omega⟩
  padding : (offset : Fin (bound - (count.val + 1))) →
    RowMatchesEncoded description
      ⟨count.val + 2 + offset.val, by
        have hcount := count.isLt
        have hoffset := offset.isLt
        omega⟩ 6 0 0

def DecodedFixedCount.source {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count) :
    BoundedCircuitKeySource n bound where
  nodeCount := ⟨count.val + 1, by omega⟩
  nodes := fun index =>
    (decoded.nodes
      ⟨index.val, by
        simpa only using index.isLt⟩).node
  output :=
    ⟨decoded.output.output.val, by
      simpa only using decoded.output.output.isLt⟩

theorem fixedCountGrammarExpr_true_decodes {n bound : ℕ}
    (description : BitInput (descriptionWidth n bound))
    (count : Fin bound)
    (htrue : (fixedCountGrammarExpr count).eval description = true) :
    Nonempty (DecodedFixedCount description count) := by
  classical
  rw [fixedCountGrammarExpr, BoolExpr.eval_all,
    List.all_eq_true] at htrue
  have hnodes :
      ∀ index : Fin (count.val + 1),
        (nodeRowExpr
          (n := n) (bound := bound)
          ⟨index.val, by omega⟩).eval description = true := by
    intro index
    apply htrue
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have houtput :
      (outputRowExpr
        (n := n) (bound := bound)
        ⟨count.val + 1, by omega⟩).eval description = true := by
    apply htrue
    apply List.mem_append_right
    simp
  have hpadding :
      ∀ offset : Fin (bound - (count.val + 1)),
        (paddingRowExpr
          (n := n) (bound := bound)
          ⟨count.val + 2 + offset.val, by omega⟩).eval
            description = true := by
    intro offset
    apply htrue
    apply List.mem_append_right
    simp only [List.mem_cons]
    exact Or.inr (List.mem_ofFn.mpr ⟨offset, rfl⟩)
  exact ⟨
    { nodes := fun index =>
        Classical.choice
          (nodeRowExpr_true_decodes description
            ⟨index.val, by omega⟩ (hnodes index))
      output :=
        Classical.choice
          (outputRowExpr_true_decodes description
            ⟨count.val + 1, by omega⟩ houtput)
      padding := fun offset =>
        paddingRowExpr_true_encoding description
          ⟨count.val + 2 + offset.val, by omega⟩
          (hpadding offset) }⟩

/-- Row evidence determines every bit, not merely the three guard outputs.
This is the key anti-phantom property used by canonical SAT recovery. -/
theorem RowMatchesEncoded.bit {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {row : Fin (bound + 1)} {tag first second : ℕ}
    (encoding : RowMatchesEncoded description row tag first second)
    (offset : Fin (rowWidth n bound)) :
    description (descriptionIndex row offset) =
      (encodedDescriptionRow n bound tag first second)[offset.val]'(by
        simpa only [encodedDescriptionRow_length] using offset.isLt) := by
  by_cases htagOffset : offset.val < 6
  · let tagOffset : Fin 6 := ⟨offset.val, htagOffset⟩
    have hbit :=
      unaryEqualsExpr_true_bits row 0 6 tag
        (by simp [rowWidth]) description encoding.tagTrue tagOffset
    unfold encodedDescriptionRow
    rw [List.getElem_append_left (by
          simp [orderedNatBits]
          omega),
      List.getElem_append_left (by
        simpa [orderedNatBits] using htagOffset)]
    simpa [orderedNatBits, tagOffset] using hbit
  · by_cases hfirstOffset :
        offset.val < 6 + boundedCircuitFieldLimit n bound
    · let firstOffset : Fin (boundedCircuitFieldLimit n bound) :=
        ⟨offset.val - 6, by omega⟩
      have hbit :=
        unaryEqualsExpr_true_bits row 6
          (boundedCircuitFieldLimit n bound) first
          (by
            simp [rowWidth]
            omega)
          description encoding.firstTrue firstOffset
      have hoffsetEq :
          (⟨6 + firstOffset.val, by
              have heq : 6 + firstOffset.val = offset.val := by
                change 6 + (offset.val - 6) = offset.val
                omega
              simpa only [heq] using offset.isLt⟩ :
            Fin (rowWidth n bound)) = offset := by
        apply Fin.ext
        change 6 + (offset.val - 6) = offset.val
        omega
      rw [hoffsetEq] at hbit
      unfold encodedDescriptionRow
      rw [List.getElem_append_left (by
          simp [orderedNatBits]
          omega),
        List.getElem_append_right (by
          simp [orderedNatBits]
          omega)]
      simpa [orderedNatBits, firstOffset] using hbit
    · let secondOffset : Fin (boundedCircuitFieldLimit n bound) :=
        ⟨offset.val -
            (6 + boundedCircuitFieldLimit n bound), by
          have hwidth :
              offset.val <
                6 + 2 * boundedCircuitFieldLimit n bound := by
            simpa only [rowWidth] using offset.isLt
          omega⟩
      have hbit :=
        unaryEqualsExpr_true_bits row
          (6 + boundedCircuitFieldLimit n bound)
          (boundedCircuitFieldLimit n bound) second
          (by
            simp [rowWidth]
            omega)
          description encoding.secondTrue secondOffset
      have hoffsetEq :
          (⟨6 + boundedCircuitFieldLimit n bound +
              secondOffset.val, by
                have heq :
                    6 + boundedCircuitFieldLimit n bound +
                        secondOffset.val =
                      offset.val := by
                  change
                    6 + boundedCircuitFieldLimit n bound +
                        (offset.val -
                          (6 + boundedCircuitFieldLimit n bound)) =
                      offset.val
                  omega
                simpa only [heq] using offset.isLt⟩ :
            Fin (rowWidth n bound)) = offset := by
        apply Fin.ext
        change
          6 + boundedCircuitFieldLimit n bound +
              (offset.val -
                (6 + boundedCircuitFieldLimit n bound)) =
            offset.val
        omega
      rw [hoffsetEq] at hbit
      unfold encodedDescriptionRow
      rw [List.getElem_append_right (by
          simp [orderedNatBits]
          omega)]
      simpa [orderedNatBits, secondOffset] using hbit

@[simp] theorem DecodedFixedCount.source_size {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count) :
    decoded.source.toCircuit.size = count.val + 1 := by
  simp [DecodedFixedCount.source, BoundedCircuitKeySource.toCircuit,
    BooleanCircuit.size]

@[simp] theorem DecodedFixedCount.source_nodes_length {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count) :
    decoded.source.toCircuit.nodes.length = count.val + 1 := by
  simpa only [BooleanCircuit.size] using decoded.source_size

@[simp] theorem DecodedFixedCount.source_node {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count)
    (index : Fin (count.val + 1)) :
    decoded.source.toCircuit.nodes.get
        (Fin.cast decoded.source_nodes_length.symm index) =
      (decoded.nodes index).node.toNode := by
  simp only [DecodedFixedCount.source,
    BoundedCircuitKeySource.toCircuit]
  rw [List.get_ofFn]
  rfl

@[simp] theorem DecodedFixedCount.source_output {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count) :
    decoded.source.toCircuit.output.val =
      decoded.output.output.val := by
  rfl

theorem descriptionIndex_surjective {n bound : ℕ}
    (index : Fin (descriptionWidth n bound)) :
    ∃ (row : Fin (bound + 1)) (offset : Fin (rowWidth n bound)),
      descriptionIndex row offset = index := by
  have hwidth : 0 < rowWidth n bound := by
    simp [rowWidth, boundedCircuitFieldLimit]
  let rowValue := index.val / rowWidth n bound
  have hrow : rowValue < bound + 1 := by
    apply Nat.div_lt_of_lt_mul
    simpa only [descriptionWidth, boundedCircuitDescriptionWidth,
      rowWidth, Nat.mul_comm] using index.isLt
  let offsetValue := index.val % rowWidth n bound
  have hoffset : offsetValue < rowWidth n bound :=
    Nat.mod_lt _ hwidth
  refine
    ⟨⟨rowValue, hrow⟩, ⟨offsetValue, hoffset⟩, ?_⟩
  apply Fin.ext
  change
    index.val / rowWidth n bound * rowWidth n bound +
        index.val % rowWidth n bound =
      index.val
  have hdivision :=
    Nat.mod_add_div index.val (rowWidth n bound)
  simpa only [Nat.add_comm, Nat.mul_comm] using hdivision

private theorem getElem_eq_of_list_eq {α : Type}
    {left right : List α} (heq : left = right) (index : ℕ)
    (hleft : index < left.length) (hright : index < right.length) :
    left[index]'hleft = right[index]'hright := by
  subst right
  rfl

/-- Every row of a successfully decoded branch is bit-for-bit the
corresponding canonical row of its single typed source circuit. -/
theorem DecodedFixedCount.descriptionIndex_eq_source
    {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count)
    (row : Fin (bound + 1)) (offset : Fin (rowWidth n bound)) :
    description (descriptionIndex row offset) =
      canonicalDescriptionInput decoded.source.toCircuit
        decoded.source.toCircuit_size_le
        (descriptionIndex row offset) := by
  rw [canonicalDescriptionInput_descriptionIndex]
  by_cases hnode : row.val < count.val + 1
  · let index : Fin (count.val + 1) := ⟨row.val, hnode⟩
    let decodedRow := decoded.nodes index
    have hdecodedRow :
        (⟨index.val, by omega⟩ : Fin (bound + 1)) = row := by
      apply Fin.ext
      rfl
    have hleft := decodedRow.encoding.bit offset
    let circuitIndex : Fin decoded.source.toCircuit.nodes.length :=
      Fin.cast decoded.source_nodes_length.symm index
    have hcanonical :=
      canonicalDescriptionRows_get_node
        (bound := bound) decoded.source.toCircuit circuitIndex
    have hsourceNode := decoded.source_node index
    have hcircuitIndex :
        circuitIndex =
          Fin.cast decoded.source_nodes_length.symm index := rfl
    rw [hcircuitIndex, hsourceNode] at hcanonical
    have hcanonicalRow :
        (canonicalDescriptionRows bound
          decoded.source.toCircuit)[row.val]'(by
            rw [canonicalDescriptionRows_length
              decoded.source.toCircuit
              decoded.source.toCircuit_size_le]
            exact row.isLt) =
          encodedDescriptionRow n bound
            (boundedNodeTag decodedRow.node)
            (boundedNodeFirst decodedRow.node)
            (boundedNodeSecond decodedRow.node) := by
      simpa only [circuitIndex, Fin.val_cast, index, decodedRow,
        boundedNodeDescriptionBits_bounded_eq_encoded] using hcanonical
    have hcanonicalBit :=
      getElem_eq_of_list_eq hcanonicalRow offset.val
        (by
          rw [canonicalDescriptionRows_uniform
            decoded.source.toCircuit
            ((canonicalDescriptionRows bound
              decoded.source.toCircuit)[row.val]'(by
                rw [canonicalDescriptionRows_length
                  decoded.source.toCircuit
                  decoded.source.toCircuit_size_le]
                exact row.isLt))
            (List.getElem_mem (by
              rw [canonicalDescriptionRows_length
                decoded.source.toCircuit
                decoded.source.toCircuit_size_le]
              exact row.isLt))]
          exact offset.isLt)
        (by simpa only [encodedDescriptionRow_length] using offset.isLt)
    exact hleft.trans hcanonicalBit.symm
  · by_cases houtput : row.val = count.val + 1
    · let outputRow : Fin (bound + 1) :=
        ⟨count.val + 1, by omega⟩
      have hrow : outputRow = row := by
        apply Fin.ext
        exact houtput.symm
      have hleft := decoded.output.encoding.bit offset
      have hcanonical :=
        canonicalDescriptionRows_get_output
          decoded.source.toCircuit
          decoded.source.toCircuit_size_le
      have hcanonicalRow :
          (canonicalDescriptionRows bound
            decoded.source.toCircuit)[row.val]'(by
              rw [canonicalDescriptionRows_length
                decoded.source.toCircuit
                decoded.source.toCircuit_size_le]
              exact row.isLt) =
            encodedDescriptionRow n bound 5
              decoded.output.output.val 0 := by
        simpa only [DecodedFixedCount.source_nodes_length,
          DecodedFixedCount.source_output,
          boundedOutputDescriptionBits_eq_encoded, houtput] using
            hcanonical
      have hcanonicalBit :=
        getElem_eq_of_list_eq hcanonicalRow offset.val
          (by
            rw [canonicalDescriptionRows_uniform
              decoded.source.toCircuit
              ((canonicalDescriptionRows bound
                decoded.source.toCircuit)[row.val]'(by
                  rw [canonicalDescriptionRows_length
                    decoded.source.toCircuit
                    decoded.source.toCircuit_size_le]
                  exact row.isLt))
              (List.getElem_mem (by
                rw [canonicalDescriptionRows_length
                  decoded.source.toCircuit
                  decoded.source.toCircuit_size_le]
                exact row.isLt))]
            exact offset.isLt)
          (by simpa only [encodedDescriptionRow_length] using offset.isLt)
      have hleftAtRow :
          description (descriptionIndex row offset) =
            (encodedDescriptionRow n bound 5
              decoded.output.output.val 0)[offset.val]'(by
                simpa only [encodedDescriptionRow_length] using
                  offset.isLt) := by
        rw [← hrow]
        exact hleft
      exact hleftAtRow.trans hcanonicalBit.symm
    · have hafter : count.val + 2 ≤ row.val := by
        omega
      let paddingOffset : Fin (bound - (count.val + 1)) :=
        ⟨row.val - (count.val + 2), by
          have hrowBound := row.isLt
          omega⟩
      let paddingRow : Fin (bound + 1) :=
        ⟨count.val + 2 + paddingOffset.val, by
          have hcount := count.isLt
          have hoffset := paddingOffset.isLt
          omega⟩
      have hrow : paddingRow = row := by
        apply Fin.ext
        dsimp only [paddingRow, paddingOffset]
        omega
      have hleft := (decoded.padding paddingOffset).bit offset
      let circuitOffset :
          Fin (bound - decoded.source.toCircuit.size) :=
        Fin.cast (by rw [decoded.source_size]) paddingOffset
      have hcanonical :=
        canonicalDescriptionRows_get_padding
          decoded.source.toCircuit
          decoded.source.toCircuit_size_le circuitOffset
      have hrowIndex :
          count.val + 1 + 1 +
              (row.val - (count.val + 2)) =
            row.val := by
        omega
      have hcanonicalRow :
          (canonicalDescriptionRows bound
            decoded.source.toCircuit)[row.val]'(by
              rw [canonicalDescriptionRows_length
                decoded.source.toCircuit
                decoded.source.toCircuit_size_le]
              exact row.isLt) =
            encodedDescriptionRow n bound 6 0 0 := by
        simpa only [DecodedFixedCount.source_nodes_length,
          circuitOffset, Fin.val_cast, paddingOffset,
          boundedPaddingDescriptionBits_eq_encoded, hrowIndex] using
            hcanonical
      have hcanonicalBit :=
        getElem_eq_of_list_eq hcanonicalRow offset.val
          (by
            rw [canonicalDescriptionRows_uniform
              decoded.source.toCircuit
              ((canonicalDescriptionRows bound
                decoded.source.toCircuit)[row.val]'(by
                  rw [canonicalDescriptionRows_length
                    decoded.source.toCircuit
                    decoded.source.toCircuit_size_le]
                  exact row.isLt))
              (List.getElem_mem (by
                rw [canonicalDescriptionRows_length
                  decoded.source.toCircuit
                  decoded.source.toCircuit_size_le]
                exact row.isLt))]
            exact offset.isLt)
          (by simpa only [encodedDescriptionRow_length] using offset.isLt)
      have hleftAtRow :
          description (descriptionIndex row offset) =
            (encodedDescriptionRow n bound 6 0 0)[offset.val]'(by
              simpa only [encodedDescriptionRow_length] using
                offset.isLt) := by
        rw [← hrow]
        exact hleft
      exact hleftAtRow.trans hcanonicalBit.symm

/-- No noncanonical bit-vector can pass the grammar: the entire raw
description is exactly the canonical encoding of the decoded typed circuit. -/
theorem DecodedFixedCount.description_eq_source
    {n bound : ℕ}
    {description : BitInput (descriptionWidth n bound)}
    {count : Fin bound} (decoded : DecodedFixedCount description count) :
    description =
      canonicalDescriptionInput decoded.source.toCircuit
        decoded.source.toCircuit_size_le := by
  funext index
  rcases descriptionIndex_surjective index with
    ⟨row, offset, hindex⟩
  rw [← hindex]
  exact decoded.descriptionIndex_eq_source row offset

/-- Soundness of one exact-count branch, including canonicality of the
assignment and universal verifier acceptance of the decoded source circuit. -/
theorem fixedCountValue_true_decodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : Fin bound)
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound))
    (htrue : fixedCountValue pcp input count description = true) :
    ∃ decoded : DecodedFixedCount description count,
      description =
          canonicalDescriptionInput decoded.source.toCircuit
            decoded.source.toCircuit_size_le ∧
        ∀ randomness,
          acceptsOracleCircuit pcp input decoded.source.toCircuit
            randomness = true := by
  classical
  rw [fixedCountValue, Bool.and_eq_true] at htrue
  let decoded :=
    Classical.choice
      (fixedCountGrammarExpr_true_decodes description count htrue.1)
  refine ⟨decoded, decoded.description_eq_source, ?_⟩
  intro randomness
  unfold verifierRowsValue at htrue
  rw [List.all_eq_true] at htrue
  have hrow :=
    htrue.2 randomness (mem_allRandomness randomness)
  rw [decoded.description_eq_source] at hrow
  have hcanonical :=
    verifierRowValue_canonical pcp input decoded.source.toCircuit
      decoded.source.toCircuit_size_le randomness
  have hrow' :
      verifierRowValue pcp input
          decoded.source.toCircuit.nodes.length
          (by
            simpa only [BooleanCircuit.size] using
              decoded.source.toCircuit_size_le)
          randomness
          (canonicalDescriptionInput decoded.source.toCircuit
            decoded.source.toCircuit_size_le) = true := by
    simpa only [decoded.source_nodes_length] using hrow
  rw [hcanonical] at hrow'
  exact hrow'

/-- Exact semantic contract for the structural C.12 verifier.  Satisfying
assignments are precisely canonical encodings of bounded circuits accepted on
every random string; there is no finite truth-table or callback premise. -/
theorem boundedOraclePredicate_eq_true_iff
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    boundedOraclePredicate pcp input bound description = true ↔
      ∃ (circuit : BooleanCircuit (pcp.nativeWidth n))
          (hsize : circuit.size ≤ bound),
        description = canonicalDescriptionInput circuit hsize ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness = true := by
  constructor
  · intro htrue
    rw [boundedOraclePredicate, countCasesValue,
      List.any_eq_true] at htrue
    rcases htrue with ⟨candidate, hcandidate, hcandTrue⟩
    rcases List.mem_ofFn.mp hcandidate with ⟨count, rfl⟩
    rcases fixedCountValue_true_decodes
        pcp input count description hcandTrue with
      ⟨decoded, hdescription, haccepts⟩
    refine
      ⟨decoded.source.toCircuit,
        decoded.source.toCircuit_size_le, ?_, haccepts⟩
    exact hdescription
  · rintro ⟨circuit, hsize, rfl, haccepts⟩
    exact boundedOraclePredicate_canonical_of_accepts
      pcp input circuit hsize haccepts

@[simp] theorem boundedOracleVerifierCircuit_eq_true_iff
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (description :
      BitInput (descriptionWidth (pcp.nativeWidth n) bound)) :
    (boundedOracleVerifierCircuit pcp input bound).eval description = true ↔
      ∃ (circuit : BooleanCircuit (pcp.nativeWidth n))
          (hsize : circuit.size ≤ bound),
        description = canonicalDescriptionInput circuit hsize ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness = true := by
  rw [boundedOracleVerifierCircuit_eval,
    boundedOraclePredicate_eq_true_iff]

/-! ## Single free-input CNF boundary -/

def boundedOracleRecoveryFormula
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : EncodedCNF :=
  circuitInputFormula (boundedOracleVerifierCircuit pcp input bound)

def boundedOracleRecoveryCode
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  Encodable.encode (boundedOracleRecoveryFormula pcp input bound)

theorem boundedOracleRecoveryFormula_wellSized
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    wellSizedCNFEncoding
        (boundedOracleRecoveryCode pcp input bound)
        (boundedOracleRecoveryFormula pcp input bound) = true := by
  exact circuitInputFormula_wellSized
    (boundedOracleVerifierCircuit pcp input bound)

theorem boundedOracleRecoveryFormula_sound
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (assignment : ℕ → Bool)
    (hsatisfies :
      formulaEval assignment
        (boundedOracleRecoveryFormula pcp input bound) = true) :
    ∃ (circuit : BooleanCircuit (pcp.nativeWidth n))
        (hsize : circuit.size ≤ bound),
      recoveredCircuitInput assignment =
          canonicalDescriptionInput circuit hsize ∧
        ∀ randomness,
          acceptsOracleCircuit pcp input circuit randomness = true := by
  apply
    (boundedOracleVerifierCircuit_eq_true_iff
      pcp input (recoveredCircuitInput assignment)).mp
  exact circuitInputFormula_sound
    (boundedOracleVerifierCircuit pcp input bound) assignment hsatisfies

theorem boundedOracleRecoveryFormula_complete
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hsize : circuit.size ≤ bound)
    (haccepts : ∀ randomness,
      acceptsOracleCircuit pcp input circuit randomness = true) :
    ∃ assignment : ℕ → Bool,
      recoveredCircuitInput assignment =
          canonicalDescriptionInput circuit hsize ∧
        formulaEval assignment
          (boundedOracleRecoveryFormula pcp input bound) = true := by
  apply circuitInputFormula_complete
    (boundedOracleVerifierCircuit pcp input bound)
      (canonicalDescriptionInput circuit hsize)
  rw [boundedOracleVerifierCircuit_eval]
  exact boundedOraclePredicate_canonical_of_accepts
    pcp input circuit hsize haccepts

theorem boundedOracleRecoveryFormula_satisfiable_iff
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) :
    (∃ assignment : ℕ → Bool,
      formulaEval assignment
        (boundedOracleRecoveryFormula pcp input bound) = true) ↔
      ∃ (description :
            BitInput
              (descriptionWidth (pcp.nativeWidth n) bound))
          (circuit : BooleanCircuit (pcp.nativeWidth n))
          (hsize : circuit.size ≤ bound),
        description = canonicalDescriptionInput circuit hsize ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness = true := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    rcases boundedOracleRecoveryFormula_sound
        pcp input assignment hsatisfies with
      ⟨circuit, hsize, hdescription, haccepts⟩
    exact
      ⟨recoveredCircuitInput assignment, circuit, hsize,
        hdescription, haccepts⟩
  · rintro ⟨description, circuit, hsize, hdescription, haccepts⟩
    subst description
    rcases boundedOracleRecoveryFormula_complete
        pcp input circuit hsize haccepts with
      ⟨assignment, _hdescription, hsatisfies⟩
    exact ⟨assignment, hsatisfies⟩

theorem encodedSat_boundedOracleRecoveryCode_eq_true_iff
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) :
    encodedSat (boundedOracleRecoveryCode pcp input bound) = true ↔
      ∃ (description :
            BitInput
              (descriptionWidth (pcp.nativeWidth n) bound))
          (circuit : BooleanCircuit (pcp.nativeWidth n))
          (hsize : circuit.size ≤ bound),
        description = canonicalDescriptionInput circuit hsize ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness = true := by
  rw [boundedOracleRecoveryCode, boundedOracleRecoveryFormula,
    encodedSat_circuitInputFormula_eq_true_iff]
  constructor
  · rintro ⟨description, haccepts⟩
    rcases
        (boundedOracleVerifierCircuit_eq_true_iff
          pcp input description).mp haccepts with
      ⟨circuit, hsize, hdescription, hcircuitAccepts⟩
    exact
      ⟨description, circuit, hsize, hdescription, hcircuitAccepts⟩
  · rintro ⟨description, circuit, hsize, hdescription, haccepts⟩
    exact
      ⟨description,
        (boundedOracleVerifierCircuit_eq_true_iff
          pcp input description).mpr
          ⟨circuit, hsize, hdescription, haccepts⟩⟩

/-! ## Explicit structural gate ledger -/

def fieldSelectionNodeCount {n bound : ℕ}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (count : ℕ) : ℕ :=
  guardedConditionsNodeCount <|
    List.ofFn fun index : Fin count =>
      fieldEquals row index.val

theorem fieldChoices_conditions {n bound : ℕ}
    {builder : BooleanDAGBuilder (descriptionWidth n bound)}
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder)) :
    (fieldChoices fieldEquals row values).map
        GuardedChoice.condition =
      List.ofFn fun index : Fin values.length =>
        fieldEquals row index.val := by
  apply List.ext_getElem
  · simp [fieldChoices]
  · intro index hleft hright
    simp [fieldChoices]

@[simp] theorem compileFieldSelect_addedNodes {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List (LiveWire builder)) :
    (compileFieldSelect builder fieldEquals row values).extension.suffix.length =
      fieldSelectionNodeCount fieldEquals row values.length := by
  let compiled :=
    compileGuardedAny builder (fieldChoices fieldEquals row values)
  change compiled.extension.suffix.length =
    fieldSelectionNodeCount fieldEquals row values.length
  rw [compileGuardedAny_addedNodes,
    guardedAnyNodeCount_eq_conditions,
    fieldChoices_conditions]
  rfl

/-- Exact cost of one universal-evaluator node.  Child values are referenced
as live wires, so the cost depends on the row width but not on the size of the
subcircuits that produced those values. -/
def tagSelectionNodeCount {n bound : ℕ}
    (row : Fin (bound + 1)) : ℕ :=
  guardedConditionsNodeCount (n := descriptionWidth n bound)
    [tagEqualsExpr (n := n) (bound := bound) row 0,
      tagEqualsExpr (n := n) (bound := bound) row 1,
      tagEqualsExpr (n := n) (bound := bound) row 2,
      tagEqualsExpr (n := n) (bound := bound) row 3,
      tagEqualsExpr (n := n) (bound := bound) row 4]

def universalNodeNodeCount {n bound : ℕ}
    (row : Fin (bound + 1)) (address : BitInput n)
    (priorCount : ℕ) : ℕ :=
  fieldSelectionNodeCount
      (firstFieldEqualsExpr (n := n) (bound := bound)) row priorCount +
    fieldSelectionNodeCount
      (secondFieldEqualsExpr (n := n) (bound := bound)) row priorCount +
    (firstFieldEqualsExpr (n := n) (bound := bound) row 1).nodeCount +
    (constantAddressSelectionExpr row address).nodeCount +
    3 + tagSelectionNodeCount (n := n) (bound := bound) row

@[simp] theorem compileUniversalNode_addedNodes {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n)
    (priorValues : List (LiveWire builder)) :
    (compileUniversalNode builder row address priorValues).compiled.extension.suffix.length =
      universalNodeNodeCount row address priorValues.length := by
  let left := compileFirstFieldSelect builder row priorValues
  let valuesAtLeft := liftLiveWires left.extension priorValues
  let right := compileSecondFieldSelect left.final row valuesAtLeft
  let leftAtRight := left.live.lift right.extension
  let constantValue :=
    compileExpr right.final (firstFieldEqualsExpr row 1)
  let leftAtConstant := leftAtRight.lift constantValue.extension
  let rightAtConstant := right.live.lift constantValue.extension
  let inputValue :=
    compileExpr constantValue.final
      (constantAddressSelectionExpr row address)
  let leftAtInput := leftAtConstant.lift inputValue.extension
  let rightAtInput := rightAtConstant.lift inputValue.extension
  let negated := compileNot inputValue.final leftAtInput
  let leftAtNegated := leftAtInput.lift negated.extension
  let rightAtNegated := rightAtInput.lift negated.extension
  let conjunction :=
    compileAnd negated.final leftAtNegated rightAtNegated
  let leftAtConjunction := leftAtNegated.lift conjunction.extension
  let rightAtConjunction := rightAtNegated.lift conjunction.extension
  let disjunction :=
    compileOr conjunction.final leftAtConjunction rightAtConjunction
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
  let selected := compileGuardedAny disjunction.final choices
  have hleft :
      left.extension.suffix.length =
        fieldSelectionNodeCount
          (firstFieldEqualsExpr (n := n) (bound := bound))
          row priorValues.length := by
    simpa only [left, compileFirstFieldSelect] using
      compileFieldSelect_addedNodes builder
        (firstFieldEqualsExpr (n := n) (bound := bound))
        row priorValues
  have hright :
      right.extension.suffix.length =
        fieldSelectionNodeCount
          (secondFieldEqualsExpr (n := n) (bound := bound))
          row priorValues.length := by
    rw [show right.extension.suffix.length =
        fieldSelectionNodeCount
          (secondFieldEqualsExpr (n := n) (bound := bound))
          row valuesAtLeft.length by
      simpa only [right, compileSecondFieldSelect] using
        compileFieldSelect_addedNodes left.final
          (secondFieldEqualsExpr (n := n) (bound := bound))
          row valuesAtLeft]
    simp only [valuesAtLeft, liftLiveWires_length]
  have hconstant :
      constantValue.extension.suffix.length =
        (firstFieldEqualsExpr
          (n := n) (bound := bound) row 1).nodeCount := by
    simpa only [constantValue] using
      compileExpr_addedNodes right.final
        (firstFieldEqualsExpr row 1)
  have hinput :
      inputValue.extension.suffix.length =
        (constantAddressSelectionExpr row address).nodeCount := by
    simpa only [inputValue] using
      compileExpr_addedNodes constantValue.final
        (constantAddressSelectionExpr row address)
  have hnegated : negated.extension.suffix.length = 1 := by
    simpa only [negated] using
      compileNot_addedNodes inputValue.final leftAtInput
  have hconjunction : conjunction.extension.suffix.length = 1 := by
    simpa only [conjunction] using
      compileAnd_addedNodes negated.final leftAtNegated rightAtNegated
  have hdisjunction : disjunction.extension.suffix.length = 1 := by
    simpa only [disjunction] using
      compileOr_addedNodes conjunction.final leftAtConjunction
        rightAtConjunction
  have hchoices :
      choices.map GuardedChoice.condition =
        [tagEqualsExpr row 0, tagEqualsExpr row 1,
          tagEqualsExpr row 2, tagEqualsExpr row 3,
          tagEqualsExpr row 4] := by
    rfl
  have hselected :
      selected.extension.suffix.length =
        tagSelectionNodeCount (n := n) row := by
    rw [show selected.extension.suffix.length =
        guardedAnyNodeCount choices by
      simpa only [selected] using
        compileGuardedAny_addedNodes disjunction.final choices]
    rw [guardedAnyNodeCount_eq_conditions, hchoices]
    rfl
  change
    (caseExtension.trans selected.extension).suffix.length =
      universalNodeNodeCount row address priorValues.length
  simp only [caseExtension, BooleanDAGExtension.trans,
    List.length_append, hleft, hright, hconstant, hinput,
    hnegated, hconjunction, hdisjunction, hselected,
    universalNodeNodeCount]
  omega

def universalNodesNodeCount {n bound : ℕ}
    (address : BitInput n) :
    (count : ℕ) → count ≤ bound → ℕ
  | 0, _ => 0
  | count + 1, hcount =>
      universalNodesNodeCount (bound := bound) address count (by omega) +
        universalNodeNodeCount (n := n) (bound := bound)
          ⟨count, by omega⟩ address count

@[simp] theorem compileUniversalNodes_addedNodes {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (compileUniversalNodes builder address count hcount).extension.suffix.length =
      universalNodesNodeCount address count hcount := by
  induction count with
  | zero =>
      simp [compileUniversalNodes, universalNodesNodeCount,
        BooleanDAGExtension.refl]
  | succ count inductionHypothesis =>
      simp only [compileUniversalNodes, universalNodesNodeCount,
        BooleanDAGExtension.trans, List.length_append,
        inductionHypothesis, compileUniversalNode_addedNodes,
        compileUniversalNodes_values_length]

def universalOutputNodeCount {n bound : ℕ}
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    ℕ :=
  universalNodesNodeCount address count hcount +
    fieldSelectionNodeCount
      (firstFieldEqualsExpr (n := n) (bound := bound))
      ⟨count, by omega⟩ count

@[simp] theorem compileUniversalOutput_addedNodes {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    (compileUniversalOutput builder address count hcount).compiled.extension.suffix.length =
      universalOutputNodeCount address count hcount := by
  let nodes := compileUniversalNodes builder address count hcount
  let outputRow : Fin (bound + 1) := ⟨count, by omega⟩
  let selected :=
    compileFirstFieldSelect nodes.final outputRow nodes.values
  have hnodes :
      nodes.extension.suffix.length =
        universalNodesNodeCount address count hcount := by
    simpa only [nodes] using
      compileUniversalNodes_addedNodes builder address count hcount
  have hselected :
      selected.extension.suffix.length =
        fieldSelectionNodeCount
          (firstFieldEqualsExpr (n := n) (bound := bound))
          outputRow count := by
    rw [show selected.extension.suffix.length =
        fieldSelectionNodeCount
          (firstFieldEqualsExpr (n := n) (bound := bound))
          outputRow nodes.values.length by
      simpa only [selected, compileFirstFieldSelect] using
        compileFieldSelect_addedNodes nodes.final
          (firstFieldEqualsExpr (n := n) (bound := bound))
          outputRow nodes.values]
    simp only [nodes, compileUniversalNodes_values_length]
  change
    (nodes.extension.trans selected.extension).suffix.length =
      universalOutputNodeCount address count hcount
  simp only [BooleanDAGExtension.trans, List.length_append,
    hnodes, hselected, universalOutputNodeCount]
  congr 2

def universalOutputsNodeCount {n bound : ℕ}
    (count : ℕ) (hcount : count ≤ bound) :
    List (BitInput n) → ℕ
  | [] => 0
  | address :: rest =>
      universalOutputNodeCount address count hcount +
        universalOutputsNodeCount count hcount rest

@[simp] theorem compileUniversalOutputs_addedNodes {n bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth n bound))
    (count : ℕ) (hcount : count ≤ bound)
    (addresses : List (BitInput n)) :
    (compileUniversalOutputs builder count hcount addresses).extension.suffix.length =
      universalOutputsNodeCount count hcount addresses := by
  induction addresses generalizing builder with
  | nil =>
      simp [compileUniversalOutputs, universalOutputsNodeCount,
        BooleanDAGExtension.refl]
  | cons address rest inductionHypothesis =>
      simp only [compileUniversalOutputs, universalOutputsNodeCount,
        BooleanDAGExtension.trans, List.length_append,
        compileUniversalOutput_addedNodes, inductionHypothesis]

def literalNodeCount {q : ℕ} : Literal q → ℕ
  | .positive _ => 0
  | .negative _ => 1

@[simp] theorem compileLiteral_addedNodes {q n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (literal : Literal q) :
    (compileLiteral builder values hlength literal).compiled.extension.suffix.length =
      literalNodeCount literal := by
  cases literal with
  | positive query =>
      simp [compileLiteral, literalNodeCount, BuiltWire.ofCompiled,
        LiveWire.stationary, BooleanDAGExtension.refl]
  | negative query =>
      simp [compileLiteral, literalNodeCount, BuiltWire.ofCompiled]

def clauseNodeCount {q : ℕ} (clause : Fin 3 → Literal q) : ℕ :=
  literalNodeCount (clause 0) +
    literalNodeCount (clause 1) +
    literalNodeCount (clause 2) + 2

@[simp] theorem compileClause_addedNodes {q n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clause : Fin 3 → Literal q) :
    (compileClause builder values hlength clause).compiled.extension.suffix.length =
      clauseNodeCount clause := by
  let first := compileLiteral builder values hlength (clause 0)
  let valuesAtFirst := liftLiveWires first.compiled.extension values
  let valuesAtFirstLength : valuesAtFirst.length = q := by
    dsimp only [valuesAtFirst]
    rw [liftLiveWires_length]
    exact hlength
  let second := compileLiteral first.compiled.final valuesAtFirst
    valuesAtFirstLength (clause 1)
  let firstAtSecond := first.live.lift second.compiled.extension
  let firstOrSecond :=
    compileOr second.compiled.final firstAtSecond second.live
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
  let third := compileLiteral firstOrSecond.final valuesAtDisjunction
    valuesAtDisjunctionLength (clause 2)
  let disjunctionAtThird :=
    firstOrSecond.live.lift third.compiled.extension
  let output :=
    compileOr third.compiled.final disjunctionAtThird third.live
  have hfirst :
      first.compiled.extension.suffix.length =
        literalNodeCount (clause 0) := by
    simpa only [first] using
      compileLiteral_addedNodes builder values hlength (clause 0)
  have hsecond :
      second.compiled.extension.suffix.length =
        literalNodeCount (clause 1) := by
    simpa only [second] using
      compileLiteral_addedNodes first.compiled.final valuesAtFirst
        valuesAtFirstLength (clause 1)
  have hfirstOrSecond :
      firstOrSecond.extension.suffix.length = 1 := by
    simpa only [firstOrSecond] using
      compileOr_addedNodes second.compiled.final firstAtSecond second.live
  have hthird :
      third.compiled.extension.suffix.length =
        literalNodeCount (clause 2) := by
    simpa only [third] using
      compileLiteral_addedNodes firstOrSecond.final valuesAtDisjunction
        valuesAtDisjunctionLength (clause 2)
  have houtput : output.extension.suffix.length = 1 := by
    simpa only [output] using
      compileOr_addedNodes third.compiled.final disjunctionAtThird
        third.live
  change
    ((first.compiled.extension.trans <|
      second.compiled.extension.trans <|
        firstOrSecond.extension.trans third.compiled.extension).trans
          output.extension).suffix.length =
      clauseNodeCount clause
  simp only [BooleanDAGExtension.trans, List.length_append,
    hfirst, hsecond, hfirstOrSecond, hthird, houtput,
    clauseNodeCount]
  omega

def clausesNodeCount {q : ℕ} :
    List (Fin 3 → Literal q) → ℕ
  | [] => 1
  | clause :: rest =>
      clauseNodeCount clause + clausesNodeCount rest + 1

@[simp] theorem compileClauses_addedNodes {q n : ℕ}
    (builder : BooleanDAGBuilder n)
    (values : List (LiveWire builder)) (hlength : values.length = q)
    (clauses : List (Fin 3 → Literal q)) :
    (compileClauses builder values hlength clauses).extension.suffix.length =
      clausesNodeCount clauses := by
  induction clauses generalizing builder with
  | nil =>
      simp [compileClauses, clausesNodeCount]
  | cons clause rest inductionHypothesis =>
      let head := compileClause builder values hlength clause
      let valuesAtHead :=
        liftLiveWires head.compiled.extension values
      let valuesAtHeadLength : valuesAtHead.length = q := by
        dsimp only [valuesAtHead]
        rw [liftLiveWires_length]
        exact hlength
      let tail :=
        compileClauses head.compiled.final valuesAtHead
          valuesAtHeadLength rest
      let headAtTail := head.live.lift tail.extension
      let conjunction :=
        compileAnd tail.final headAtTail tail.live
      have hhead :
          head.compiled.extension.suffix.length =
            clauseNodeCount clause := by
        simpa only [head] using
          compileClause_addedNodes builder values hlength clause
      have htail :
          tail.extension.suffix.length =
            clausesNodeCount rest := by
        simpa only [tail] using
          inductionHypothesis head.compiled.final valuesAtHead
            valuesAtHeadLength
      have hconjunction :
          conjunction.extension.suffix.length = 1 := by
        simpa only [conjunction] using
          compileAnd_addedNodes tail.final headAtTail tail.live
      change
        ((head.compiled.extension.trans tail.extension).trans
          conjunction.extension).suffix.length =
            clausesNodeCount (clause :: rest)
      simp only [BooleanDAGExtension.trans, List.length_append,
        hhead, htail, hconjunction, clausesNodeCount]

def verifierRowNodeCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) : ℕ :=
  universalOutputsNodeCount count hcount
      (projectedAddresses pcp input randomness) +
    clausesNodeCount (pcp.decision input randomness).clauses

@[simp] theorem compileVerifierRow_addedNodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (count : ℕ) (hcount : count ≤ bound)
    (randomness : BitInput (pcp.nativeWidth n)) :
    (compileVerifierRow pcp input builder count hcount
      randomness).compiled.extension.suffix.length =
      verifierRowNodeCount pcp input count hcount randomness := by
  let queries :=
    compileUniversalOutputs builder count hcount
      (projectedAddresses pcp input randomness)
  let queryLength : queries.values.length = pcp.queryCount n := by
    rw [compileUniversalOutputs_values_length,
      projectedAddresses_length]
  let decision :=
    compileClauses queries.final queries.values queryLength
      (pcp.decision input randomness).clauses
  have hqueries :
      queries.extension.suffix.length =
        universalOutputsNodeCount count hcount
          (projectedAddresses pcp input randomness) := by
    simpa only [queries] using
      compileUniversalOutputs_addedNodes builder count hcount
        (projectedAddresses pcp input randomness)
  have hdecision :
      decision.extension.suffix.length =
        clausesNodeCount (pcp.decision input randomness).clauses := by
    simpa only [decision] using
      compileClauses_addedNodes queries.final queries.values queryLength
        (pcp.decision input randomness).clauses
  change
    (queries.extension.trans decision.extension).suffix.length =
      verifierRowNodeCount pcp input count hcount randomness
  simp only [BooleanDAGExtension.trans, List.length_append,
    hqueries, hdecision, verifierRowNodeCount]

def verifierRowsNodeCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound) :
    List (BitInput (pcp.nativeWidth n)) → ℕ
  | [] => 1
  | randomness :: rest =>
      verifierRowNodeCount pcp input count hcount randomness +
        verifierRowsNodeCount pcp input count hcount rest + 1

@[simp] theorem compileVerifierRows_addedNodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (randomnessRows : List (BitInput (pcp.nativeWidth n))) :
    (compileVerifierRows pcp input count hcount builder
      randomnessRows).extension.suffix.length =
        verifierRowsNodeCount pcp input count hcount randomnessRows := by
  induction randomnessRows generalizing builder with
  | nil =>
      simp [compileVerifierRows, verifierRowsNodeCount]
  | cons randomness rest inductionHypothesis =>
      let head :=
        compileVerifierRow pcp input builder count hcount randomness
      let tail :=
        compileVerifierRows pcp input count hcount
          head.compiled.final rest
      let headAtTail := head.live.lift tail.extension
      let conjunction :=
        compileAnd tail.final headAtTail tail.live
      have hhead :
          head.compiled.extension.suffix.length =
            verifierRowNodeCount pcp input count hcount randomness := by
        simpa only [head] using
          compileVerifierRow_addedNodes pcp input builder count hcount
            randomness
      have htail :
          tail.extension.suffix.length =
            verifierRowsNodeCount pcp input count hcount rest := by
        simpa only [tail] using
          inductionHypothesis head.compiled.final
      have hconjunction :
          conjunction.extension.suffix.length = 1 := by
        simpa only [conjunction] using
          compileAnd_addedNodes tail.final headAtTail tail.live
      change
        ((head.compiled.extension.trans tail.extension).trans
          conjunction.extension).suffix.length =
            verifierRowsNodeCount pcp input count hcount
              (randomness :: rest)
      simp only [BooleanDAGExtension.trans, List.length_append,
        hhead, htail, hconjunction, verifierRowsNodeCount]

def fixedCountNodeCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) (count : Fin bound) : ℕ :=
  (fixedCountGrammarExpr
      (n := pcp.nativeWidth n) count).nodeCount +
    verifierRowsNodeCount (bound := bound) pcp input
      (count.val + 1) (by omega)
      (allRandomness (pcp.nativeWidth n)) + 1

@[simp] theorem compileFixedCount_addedNodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (count : Fin bound) :
    (compileFixedCount pcp input builder count).extension.suffix.length =
      fixedCountNodeCount pcp input count := by
  let grammar :=
    compileExpr builder
      (fixedCountGrammarExpr
        (n := pcp.nativeWidth n) count)
  let rows :=
    compileVerifierRows pcp input (count.val + 1) (by omega)
      grammar.final (allRandomness (pcp.nativeWidth n))
  let grammarAtRows := grammar.live.lift rows.extension
  let conjunction :=
    compileAnd rows.final grammarAtRows rows.live
  have hgrammar :
      grammar.extension.suffix.length =
        (fixedCountGrammarExpr
          (n := pcp.nativeWidth n) count).nodeCount := by
    simpa only [grammar] using
      compileExpr_addedNodes builder
        (fixedCountGrammarExpr
          (n := pcp.nativeWidth n) count)
  have hrows :
      rows.extension.suffix.length =
        verifierRowsNodeCount (bound := bound) pcp input
          (count.val + 1) (by omega)
          (allRandomness (pcp.nativeWidth n)) := by
    simpa only [rows] using
      compileVerifierRows_addedNodes pcp input (count.val + 1)
        (by omega) grammar.final
        (allRandomness (pcp.nativeWidth n))
  have hconjunction :
      conjunction.extension.suffix.length = 1 := by
    simpa only [conjunction] using
      compileAnd_addedNodes rows.final grammarAtRows rows.live
  change
    ((grammar.extension.trans rows.extension).trans
      conjunction.extension).suffix.length =
        fixedCountNodeCount pcp input count
  simp only [BooleanDAGExtension.trans, List.length_append,
    hgrammar, hrows, hconjunction, fixedCountNodeCount]

def countCasesNodeCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n) : List (Fin bound) → ℕ
  | [] => 1
  | count :: rest =>
      fixedCountNodeCount pcp input count +
        countCasesNodeCount pcp input rest + 1

@[simp] theorem compileCountCases_addedNodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound))
    (counts : List (Fin bound)) :
    (compileCountCases pcp input builder counts).extension.suffix.length =
      countCasesNodeCount pcp input counts := by
  induction counts generalizing builder with
  | nil =>
      simp [compileCountCases, countCasesNodeCount]
  | cons count rest inductionHypothesis =>
      let head := compileFixedCount pcp input builder count
      let tail :=
        compileCountCases pcp input head.final rest
      let headAtTail := head.live.lift tail.extension
      let disjunction :=
        compileOr tail.final headAtTail tail.live
      have hhead :
          head.extension.suffix.length =
            fixedCountNodeCount pcp input count := by
        simpa only [head] using
          compileFixedCount_addedNodes pcp input builder count
      have htail :
          tail.extension.suffix.length =
            countCasesNodeCount pcp input rest := by
        simpa only [tail] using
          inductionHypothesis head.final
      have hdisjunction :
          disjunction.extension.suffix.length = 1 := by
        simpa only [disjunction] using
          compileOr_addedNodes tail.final headAtTail tail.live
      change
        ((head.extension.trans tail.extension).trans
          disjunction.extension).suffix.length =
            countCasesNodeCount pcp input (count :: rest)
      simp only [BooleanDAGExtension.trans, List.length_append,
        hhead, htail, hdisjunction, countCasesNodeCount]

/-- Closed-form structural budget consumed by the one public C.12 verifier.
It is a recurrence over rows, queries, and decision clauses—not a restatement
of the already-built circuit's size. -/
def boundedOracleStructuralGateBudget
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  countCasesNodeCount (bound := bound) pcp input
    (List.ofFn (id : Fin bound → Fin bound))

@[simp] theorem compileBoundedOracleVerifier_addedNodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ)
    (builder :
      BooleanDAGBuilder
        (descriptionWidth (pcp.nativeWidth n) bound)) :
    (compileBoundedOracleVerifier pcp input bound builder).extension.suffix.length =
    boundedOracleStructuralGateBudget pcp input bound := by
  simpa only [compileBoundedOracleVerifier,
    boundedOracleStructuralGateBudget] using
    compileCountCases_addedNodes pcp input builder
      (List.ofFn (id : Fin bound → Fin bound))

theorem boundedOracleVerifierCircuit_size
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (boundedOracleVerifierCircuit pcp input bound).size =
      boundedOracleStructuralGateBudget pcp input bound := by
  let builder :=
    BooleanDAGBuilder.empty
      (descriptionWidth (pcp.nativeWidth n) bound)
  let compiled :=
    compileBoundedOracleVerifier pcp input bound builder
  change compiled.final.nodes.length =
    boundedOracleStructuralGateBudget pcp input bound
  rw [compiled.extension.length_eq]
  have hadd :
      compiled.extension.suffix.length =
        boundedOracleStructuralGateBudget pcp input bound := by
    simpa only [compiled, builder] using
      compileBoundedOracleVerifier_addedNodes pcp input bound builder
  simp only [builder, BooleanDAGBuilder.empty, List.length_nil,
    Nat.zero_add, hadd]

end NearCubicWires.BoundedOracleStructuralCircuit

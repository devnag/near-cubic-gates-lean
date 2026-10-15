import Proof.Circuits.BoundedOracleStructuralNodeSchedule
import Proof.PCP.BoundedOracleStructuralProjectionTable

/-!
# Table-driven bounded-oracle structural compiler

This is the data boundary used by the executable atom indexer.  The compiler
below consumes only the public shape `(width, queryCount)`, a decoded projection
table, and the circuit bound.  It deliberately reuses the canonical
`BooleanDAGBuilder` operations; there is no second gate representation or
alternate Tseitin schedule.

Correctness proofs and semantic functions stored in `BuiltWire` are erased from
the runtime ABI.  The structural result still contains the exact append-only
builder, extension, and output wire needed to identify the canonical formula.
-/

namespace NearCubicWires.BoundedOracleStructuralTableCompiler

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces

def tableRandomness (width code : ℕ) : BitInput width :=
  fun bit => code.testBit bit.val

def tableProjectedAddresses
    (outputs : List ℕ) (width count randomnessCode : ℕ) :
    List (BitInput width) :=
  List.ofFn fun query : Fin count =>
    projectionTableAddress outputs width query.val
      (tableRandomness width randomnessCode)

@[simp] theorem tableProjectedAddresses_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode : ℕ) :
    tableProjectedAddresses (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) randomnessCode =
      projectedAddresses pcp.toSemantic input
        (tableRandomness (pcp.nativeWidth n) randomnessCode) := by
  simpa only [tableProjectedAddresses] using
    projectionTableAddresses_runnerOutputs pcp input
      (tableRandomness (pcp.nativeWidth n) randomnessCode)

/-- The sole structural implementation of one verifier row.  Making addresses
an indexed function keeps the query-count invariant in the type and avoids a
second list-shape proof at every caller. -/
def verifierRowDataValue
    {width count bound : ℕ}
    (address : Fin count → BitInput width)
    (decisionFormula : ThreeCNF count)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (description : BitInput (descriptionWidth width bound)) : Bool :=
  decisionFormula.eval fun query =>
    universalOutputValue (address query) nodeCount hnodeCount description

def compileVerifierRowData
    (width count bound : ℕ)
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (address : Fin count → BitInput width)
    (decisionFormula : ThreeCNF count) : BuiltWire builder :=
  let addresses := List.ofFn address
  let queries :=
    compileUniversalOutputs builder nodeCount hnodeCount addresses
  let queryLength : queries.values.length = count := by
    rw [compileUniversalOutputs_values_length]
    simp [addresses]
  let decision :=
    compileClauses queries.final queries.values queryLength
      decisionFormula.clauses
  let result := decision.prepend queries.extension
  { function :=
      verifierRowDataValue address decisionFormula nodeCount hnodeCount
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
            builder nodeCount hnodeCount addresses (by simp [addresses])
            queryLength description]
          funext query
          simp [addresses] } }

/-- Compile one verifier row from the actual outputs of the imported runners. -/
def compileTableVerifierRow
    (outputs : List ℕ) (width count bound : ℕ)
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCode : ℕ) : BuiltWire builder :=
  compileVerifierRowData width count bound builder nodeCount hnodeCount
    (fun query =>
      projectionTableAddress outputs width query.val
        (tableRandomness width randomnessCode))
    (projectionTableDecision outputs width count randomnessCode)

theorem compileTableVerifierRow_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder : BooleanDAGBuilder
      (descriptionWidth (pcp.nativeWidth n) bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCode : ℕ)
    (hrandomnessCode : randomnessCode < 2 ^ pcp.nativeWidth n) :
    compileTableVerifierRow (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound builder
        nodeCount hnodeCount randomnessCode =
      compileVerifierRow pcp.toSemantic input builder nodeCount hnodeCount
        (tableRandomness (pcp.nativeWidth n) randomnessCode) := by
  have haddresses :
      (fun query : Fin (pcp.queryCount n) =>
        projectionTableAddress (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) query.val
          (tableRandomness (pcp.nativeWidth n) randomnessCode)) =
        fun query =>
          projectedInput pcp.toSemantic input
            (tableRandomness (pcp.nativeWidth n) randomnessCode) query := by
    funext query
    exact projectionTableAddress_runnerOutputs pcp input
      (tableRandomness (pcp.nativeWidth n) randomnessCode) query
  have hdecision :
      projectionTableDecision (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) randomnessCode =
        pcp.decision input
          (tableRandomness (pcp.nativeWidth n) randomnessCode) := by
    change
      projectionTableDecision (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) randomnessCode =
        pcp.decision input (fun bit =>
          randomnessCode.testBit bit.val)
    exact projectionTableDecision_runnerOutputs pcp input randomnessCode
      hrandomnessCode
  rw [compileTableVerifierRow, haddresses, hdecision]
  unfold compileVerifierRowData compileVerifierRow verifierRowDataValue
    verifierRowValue describedQueryAssignment projectedAddresses
  simp only [ExecutableProjectionPCP.toSemantic]

/-- Rows are compiled in increasing binary order, matching `allRandomness`. -/
def compileTableVerifierRows
    (outputs : List ℕ) (width count bound : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    (builder : BooleanDAGBuilder (descriptionWidth width bound)) →
      List ℕ → BuiltWire builder
  | builder, [] =>
      BuiltWire.ofCompiled (compileConst builder true)
  | builder, randomnessCode :: rest =>
      let head :=
        compileTableVerifierRow outputs width count bound builder
          nodeCount hnodeCount randomnessCode
      let tail :=
        compileTableVerifierRows outputs width count bound
          nodeCount hnodeCount head.compiled.final rest
      let headAtTail := head.live.lift tail.compiled.extension
      let conjunction :=
        compileAnd tail.compiled.final headAtTail tail.live
      BuiltWire.ofCompiled <|
        conjunction.prepend <|
          head.compiled.extension.trans tail.compiled.extension

theorem compileTableVerifierRows_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (builder : BooleanDAGBuilder
      (descriptionWidth (pcp.nativeWidth n) bound))
    (randomnessCodes : List ℕ)
    (hcodes :
      ∀ code ∈ randomnessCodes, code < 2 ^ pcp.nativeWidth n) :
    compileTableVerifierRows (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound nodeCount hnodeCount
        builder randomnessCodes =
      BuiltWire.ofCompiled
        (compileVerifierRows pcp.toSemantic input nodeCount hnodeCount builder
          (randomnessCodes.map
            (tableRandomness (pcp.nativeWidth n)))) := by
  induction randomnessCodes generalizing builder with
  | nil =>
      rfl
  | cons randomnessCode rest inductionHypothesis =>
      have hcode : randomnessCode < 2 ^ pcp.nativeWidth n :=
        hcodes randomnessCode (by simp)
      have hrest :
          ∀ code ∈ rest, code < 2 ^ pcp.nativeWidth n := by
        intro code hmember
        exact hcodes code (by simp [hmember])
      simp only [compileTableVerifierRows, List.map_cons,
        compileVerifierRows]
      rw [compileTableVerifierRow_eq pcp input builder nodeCount hnodeCount
        randomnessCode hcode]
      rw [inductionHypothesis _ hrest]
      rfl

/-- Close one already-compiled row family under the canonical grammar guard. -/
def compileFixedCountWithRows
    {width bound : ℕ}
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (candidate : Fin bound)
    (rows : BuiltWire
      (compileExpr builder
        (fixedCountGrammarExpr (n := width) candidate)).final) :
    BuiltWire builder :=
  let grammar :=
    compileExpr builder
      (fixedCountGrammarExpr (n := width) candidate)
  let grammarAtRows := grammar.live.lift rows.compiled.extension
  let conjunction :=
    compileAnd rows.compiled.final grammarAtRows rows.live
  BuiltWire.ofCompiled <|
    conjunction.prepend <|
      grammar.extension.trans rows.compiled.extension

/-- One candidate circuit-size case: canonical grammar, all table-driven
verifier rows, then their conjunction. -/
def compileTableFixedCount
    (outputs : List ℕ) (width count bound : ℕ)
    (builder : BooleanDAGBuilder (descriptionWidth width bound))
    (candidate : Fin bound) : BuiltWire builder :=
  compileFixedCountWithRows builder candidate <|
    compileTableVerifierRows outputs width count bound
      (candidate.val + 1) (by omega)
      (compileExpr builder
        (fixedCountGrammarExpr (n := width) candidate)).final
      (List.range (2 ^ width))

theorem compileTableFixedCount_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder : BooleanDAGBuilder
      (descriptionWidth (pcp.nativeWidth n) bound))
    (candidate : Fin bound) :
    compileTableFixedCount (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound builder candidate =
      BuiltWire.ofCompiled
        (compileFixedCount pcp.toSemantic input builder candidate) := by
  have hrows :=
    compileTableVerifierRows_eq pcp input (candidate.val + 1)
      (by omega)
      (compileExpr builder
        (fixedCountGrammarExpr (n := pcp.nativeWidth n) candidate)).final
      (List.range (2 ^ pcp.nativeWidth n)) (by
      intro code hcode
      exact List.mem_range.mp hcode)
  unfold compileTableFixedCount
  rw [hrows]
  unfold compileFixedCountWithRows compileFixedCount fixedCountValue
    verifierRowsValue allRandomness tableRandomness
  rfl

/-- All legal candidate sizes are ORed in the canonical increasing order. -/
def compileTableCountCases
    (outputs : List ℕ) (width count bound : ℕ) :
    (builder : BooleanDAGBuilder (descriptionWidth width bound)) →
      List (Fin bound) → BuiltWire builder
  | builder, [] =>
      BuiltWire.ofCompiled (compileConst builder false)
  | builder, candidate :: rest =>
      let head :=
        compileTableFixedCount outputs width count bound builder candidate
      let tail :=
        compileTableCountCases outputs width count bound
          head.compiled.final rest
      let headAtTail := head.live.lift tail.compiled.extension
      let disjunction :=
        compileOr tail.compiled.final headAtTail tail.live
      BuiltWire.ofCompiled <|
        disjunction.prepend <|
          head.compiled.extension.trans tail.compiled.extension

theorem compileTableCountCases_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n bound : ℕ}
    (input : BitInput n)
    (builder : BooleanDAGBuilder
      (descriptionWidth (pcp.nativeWidth n) bound))
    (candidates : List (Fin bound)) :
    compileTableCountCases (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound builder candidates =
      BuiltWire.ofCompiled
        (compileCountCases pcp.toSemantic input builder candidates) := by
  induction candidates generalizing builder with
  | nil =>
      rfl
  | cons candidate rest inductionHypothesis =>
      simp only [compileTableCountCases, compileCountCases]
      rw [compileTableFixedCount_eq pcp input builder candidate]
      rw [inductionHypothesis _]
      rfl

def compileTableBoundedOracleVerifier
    (outputs : List ℕ) (width count bound : ℕ)
    (builder : BooleanDAGBuilder (descriptionWidth width bound)) :
    BuiltWire builder :=
  compileTableCountCases outputs width count bound builder (List.ofFn id)

theorem compileTableBoundedOracleVerifier_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ)
    (builder : BooleanDAGBuilder
      (descriptionWidth (pcp.nativeWidth n) bound)) :
    compileTableBoundedOracleVerifier
        (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound builder =
      BuiltWire.ofCompiled
        (compileBoundedOracleVerifier pcp.toSemantic input bound builder) := by
  unfold compileTableBoundedOracleVerifier compileBoundedOracleVerifier
  exact compileTableCountCases_eq pcp input builder (List.ofFn id)

def tableBoundedOracleVerifierCircuit
    (outputs : List ℕ) (width count bound : ℕ) :
    BooleanCircuit (descriptionWidth width bound) :=
  let compiled :=
    compileTableBoundedOracleVerifier outputs width count bound <|
      BooleanDAGBuilder.empty (descriptionWidth width bound)
  compiled.compiled.final.finish compiled.compiled.output

def tableBoundedOracleStructuralNodeSchedule
    (outputs : List ℕ) (width count bound : ℕ) :
    List (BooleanNode (descriptionWidth width bound)) :=
  (compileTableBoundedOracleVerifier outputs width count bound <|
    BooleanDAGBuilder.empty
      (descriptionWidth width bound)).compiled.extension.suffix

def tableBoundedOracleStructuralOutputIndex
    (outputs : List ℕ) (width count bound : ℕ) : ℕ :=
  (compileTableBoundedOracleVerifier outputs width count bound <|
    BooleanDAGBuilder.empty
      (descriptionWidth width bound)).compiled.output.val

@[simp] theorem tableBoundedOracleVerifierCircuit_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    tableBoundedOracleVerifierCircuit (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound =
      boundedOracleVerifierCircuit pcp.toSemantic input bound := by
  unfold tableBoundedOracleVerifierCircuit boundedOracleVerifierCircuit
  rw [compileTableBoundedOracleVerifier_eq]
  rfl

@[simp] theorem tableBoundedOracleStructuralNodeSchedule_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    tableBoundedOracleStructuralNodeSchedule
        (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound =
      boundedOracleStructuralNodeSchedule pcp.toSemantic input bound := by
  unfold tableBoundedOracleStructuralNodeSchedule
    boundedOracleStructuralNodeSchedule
  rw [compileTableBoundedOracleVerifier_eq]
  rfl

@[simp] theorem tableBoundedOracleStructuralOutputIndex_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    tableBoundedOracleStructuralOutputIndex
        (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound =
      boundedOracleStructuralOutputIndex pcp.toSemantic input bound := by
  unfold tableBoundedOracleStructuralOutputIndex
    boundedOracleStructuralOutputIndex
  rw [compileTableBoundedOracleVerifier_eq]
  rfl

@[simp] theorem tableBoundedOracleStructuralNodeSchedule_eq_nodes
    (outputs : List ℕ) (width count bound : ℕ) :
    tableBoundedOracleStructuralNodeSchedule outputs width count bound =
      (tableBoundedOracleVerifierCircuit outputs width count bound).nodes := by
  let builder :=
    BooleanDAGBuilder.empty (descriptionWidth width bound)
  let compiled :=
    compileTableBoundedOracleVerifier outputs width count bound builder
  have hnodes := compiled.compiled.extension.nodes_eq
  change compiled.compiled.extension.suffix =
    compiled.compiled.final.nodes
  simpa only [builder, BooleanDAGBuilder.empty, List.nil_append] using
    hnodes.symm

@[simp] theorem tableBoundedOracleStructuralOutputIndex_eq_output
    (outputs : List ℕ) (width count bound : ℕ) :
    tableBoundedOracleStructuralOutputIndex outputs width count bound =
      (tableBoundedOracleVerifierCircuit outputs width count bound).output.val :=
  rfl

end NearCubicWires.BoundedOracleStructuralTableCompiler

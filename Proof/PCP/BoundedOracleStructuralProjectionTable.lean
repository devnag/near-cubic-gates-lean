import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.ProjectionRunnerBalancedProgram
import Proof.Foundations.VerifiedLinker

/-!
# Public projection-table semantics for the bounded-oracle compiler

The executable projection runner returns one balanced table: query-coordinate
outputs in row-major order, followed by one decision output for every random
string.  This module gives that table its sole structural interpretation.  In
particular, the compiler-facing functions below decode the actual runner
outputs; they do not invoke either imported runner a second time.
-/

namespace NearCubicWires.BoundedOracleStructuralProjectionTable

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.ProjectionRunnerCallProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-- The raw imported result is the left field of a context-preserving runner
output. -/
def projectionRawOutput (output : ℕ) : ℕ :=
  (Nat.unpair output).1

/-! ## Fixed access to the balanced public table -/

/-- After the canonical balanced lookup, erase the runner-call wrapper and
return only its left payload.  This is the sole executable table-read ABI used
by the structural compiler. -/
def projectionRawOutputSuffixProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

def projectionRawOutputLookupProgram : NPOracleProgram :=
  linkPrograms canonicalBalancedLookupProgram
    projectionRawOutputSuffixProgram

theorem projectionRawOutputLookupProgram_oracleFree :
    OracleFree projectionRawOutputLookupProgram := by
  apply oracleFree_linkPrograms
    canonicalBalancedLookupProgram_oracleFree
  rfl

def projectionRawOutputLookupFuel
    (outputs : List ℕ) (index : ℕ) : ℕ :=
  linkFuel projectionRawOutputSuffixProgram
    (balancedLookupFuel outputs index) 2

def projectionRawOutputLookupBits
    (inputLength : ℕ) (outputs : List ℕ) (index : ℕ) : ℕ :=
  max (natBitLength inputLength)
    (balancedLookupMaximumBits outputs index)

theorem projectionRawOutputLookupFuel_le
    (outputs : List ℕ) (index : ℕ)
    (hindex : index < outputs.length) :
    projectionRawOutputLookupFuel outputs index ≤
      27 * (outputs.length + 1) + 9 := by
  rw [projectionRawOutputLookupFuel,
    linkFuel_exact]
  have hlookup := balancedLookupFuel_le outputs index hindex
  norm_num [projectionRawOutputSuffixProgram,
    programRegisterSpan, instructionRegisterSpan,
    instructionRegisters] at *
  omega

theorem run_projectionRawOutputSuffixProgram
    (inputLength output maximumBits : ℕ)
    (houtput : natBitLength output ≤ maximumBits) :
    runNPOracleProgram projectionRawOutputSuffixProgram maximumBits 2
        (initialNPOracleState inputLength output) =
      some (projectionRawOutput output) := by
  have hraw :
      natBitLength (Nat.unpair output).1 ≤ maximumBits :=
    (PolynomialClock.natBitLength_mono
      (Nat.unpair_left_le output)).trans houtput
  simp [projectionRawOutputSuffixProgram, projectionRawOutput,
    runNPOracleProgram, initialNPOracleState,
    NPOracleState.boundedWrite, hraw]

/-- Exact fixed-machine lookup from the canonical balanced table.  The caller
provides only its public length, index, and code; no decoded list or callback
crosses the executable boundary. -/
theorem run_projectionRawOutputLookupProgram
    (inputLength : ℕ) (outputs : List ℕ) (index : ℕ)
    (hindex : index < outputs.length) :
    runNPOracleProgram projectionRawOutputLookupProgram
        (projectionRawOutputLookupBits inputLength outputs index)
        (projectionRawOutputLookupFuel outputs index)
        (initialNPOracleState inputLength
          (balancedLookupInput outputs index)) =
      some (projectionRawOutput outputs[index]) := by
  let maximumBits :=
    projectionRawOutputLookupBits inputLength outputs index
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans
        (Nat.le_max_left _ _)
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hlookupBits :
      balancedLookupMaximumBits outputs index ≤ maximumBits :=
    Nat.le_max_right _ _
  have hfirst :
      runNPOracleProgram canonicalBalancedLookupProgram maximumBits
          (balancedLookupFuel outputs index)
          (initialNPOracleState inputLength
            (balancedLookupInput outputs index)) =
        some outputs[index] :=
    run_bits_mono
      (run_canonicalBalancedLookupProgram outputs index inputLength hindex)
      hlookupBits
  have houtputBits :
      natBitLength outputs[index] ≤ maximumBits := by
    exact run_output_bounded hfirst
  apply run_linkPrograms hpositive hlengthBits hfirst
  exact run_projectionRawOutputSuffixProgram
    inputLength outputs[index] maximumBits houtputBits

/-- Row-major query offset shared by the producer and the structural compiler. -/
def projectionQueryOffset (width query bit : ℕ) : ℕ :=
  query * width + bit

/-- Decision rows follow the complete query-coordinate rectangle. -/
def projectionDecisionOffset
    (width count randomnessCode : ℕ) : ℕ :=
  count * width + randomnessCode

private theorem rowMajorOffset_lt
    {width count query bit : ℕ}
    (hquery : query < count) (hbit : bit < width) :
    query * width + bit < count * width := by
  calc
    query * width + bit < query * width + width :=
      Nat.add_lt_add_left hbit _
    _ = (query + 1) * width := by
      rw [Nat.add_mul]
      simp
    _ ≤ count * width :=
      Nat.mul_le_mul_right width (Nat.succ_le_iff.mpr hquery)

private theorem projectionQueryTableOutputs_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionQueryTableOutputs pcp input).length =
      pcp.queryCount n * pcp.nativeWidth n := by
  have hlength := congrArg List.length
    (projectionQueryCalls_outputs pcp input)
  simpa only [List.length_map, projectionQueryCalls_length] using
    hlength.symm

private theorem projectionDecisionTableOutputs_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionDecisionTableOutputs pcp input).length =
      2 ^ pcp.nativeWidth n := by
  have hlength := congrArg List.length
    (projectionDecisionCalls_outputs pcp input)
  simpa only [List.length_map, projectionDecisionCalls_length] using
    hlength.symm

private theorem projectionRunnerCallOutputs_eq_tables
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    projectionRunnerCallOutputs pcp input =
      projectionQueryTableOutputs pcp input ++
        projectionDecisionTableOutputs pcp input := by
  simpa only [projectionRunnerCallOutputs] using
    projectionRunnerCalls_outputs pcp input

private theorem getElem_projectionQueryTableOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    (projectionQueryTableOutputs pcp input)[
        projectionQueryOffset (pcp.nativeWidth n) query.val bit.val]'(by
          rw [projectionQueryTableOutputs_length]
          exact rowMajorOffset_lt query.isLt bit.isLt) =
      ProjectionRunnerCall.output pcp
        (.query (pcp.queryRequest input query bit)) := by
  unfold projectionQueryTableOutputs projectionQueryOffset
  rw [getElem_flatten_uniform
    (List.ofFn fun query : Fin (pcp.queryCount n) =>
      List.ofFn fun bit : Fin (pcp.nativeWidth n) =>
        ProjectionRunnerCall.output pcp
          (.query (pcp.queryRequest input query bit)))
    (pcp.nativeWidth n) query.val bit.val]
  · simp
  · intro row hrow
    rw [List.mem_ofFn] at hrow
    obtain ⟨index, rfl⟩ := hrow
    simp
  · simp
  · exact bit.isLt

private theorem getD_projectionRunnerCallOutputs_query
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    (projectionRunnerCallOutputs pcp input).getD
        (projectionQueryOffset (pcp.nativeWidth n) query.val bit.val) 0 =
      ProjectionRunnerCall.output pcp
        (.query (pcp.queryRequest input query bit)) := by
  rw [projectionRunnerCallOutputs_eq_tables pcp input]
  rw [List.getD_append _ _ _ _ (by
    rw [projectionQueryTableOutputs_length]
    exact rowMajorOffset_lt query.isLt bit.isLt)]
  rw [List.getD_eq_getElem _ _ (by
    rw [projectionQueryTableOutputs_length]
    exact rowMajorOffset_lt query.isLt bit.isLt)]
  exact getElem_projectionQueryTableOutputs pcp input query bit

private theorem allRandomness_getElem
    (width randomnessCode : ℕ) (hrandomnessCode : randomnessCode < 2 ^ width) :
    (allRandomness width)[randomnessCode]'(by simpa) =
      fun bit : Fin width => randomnessCode.testBit bit.val := by
  simp [allRandomness]

private theorem getElem_projectionDecisionTableOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode : ℕ)
    (hrandomnessCode : randomnessCode < 2 ^ pcp.nativeWidth n) :
    (projectionDecisionTableOutputs pcp input)[randomnessCode]'(by
      simp [projectionDecisionTableOutputs, hrandomnessCode]) =
      ProjectionRunnerCall.output pcp
        (.decision (pcp.decisionRequest input fun bit =>
          randomnessCode.testBit bit.val)) := by
  unfold projectionDecisionTableOutputs
  simp only [List.getElem_map]
  rw [allRandomness_getElem _ _ hrandomnessCode]

private theorem getD_projectionRunnerCallOutputs_decision
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode : ℕ)
    (hrandomnessCode : randomnessCode < 2 ^ pcp.nativeWidth n) :
    (projectionRunnerCallOutputs pcp input).getD
        (projectionDecisionOffset (pcp.nativeWidth n)
          (pcp.queryCount n) randomnessCode) 0 =
      ProjectionRunnerCall.output pcp
        (.decision (pcp.decisionRequest input fun bit =>
          randomnessCode.testBit bit.val)) := by
  rw [projectionRunnerCallOutputs_eq_tables pcp input]
  rw [List.getD_append_right _ _ _ _ (by
    rw [projectionQueryTableOutputs_length]
    simp [projectionDecisionOffset])]
  rw [show
      projectionDecisionOffset (pcp.nativeWidth n)
          (pcp.queryCount n) randomnessCode -
        (projectionQueryTableOutputs pcp input).length =
          randomnessCode by
    rw [projectionQueryTableOutputs_length]
    simp [projectionDecisionOffset]]
  rw [List.getD_eq_getElem _ _ (by
    rw [projectionDecisionTableOutputs_length]
    exact hrandomnessCode)]
  exact
    getElem_projectionDecisionTableOutputs pcp input randomnessCode
      hrandomnessCode

@[simp] theorem projectionRunnerCallOutputs_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionRunnerCallOutputs pcp input).length =
      pcp.queryCount n * pcp.nativeWidth n +
        2 ^ pcp.nativeWidth n := by
  rw [projectionRunnerCallOutputs_eq_tables,
    List.length_append, projectionQueryTableOutputs_length,
    projectionDecisionTableOutputs_length]

/-- A fixed balanced-table read returns the exact published query-runner
payload at one row-major coordinate. -/
theorem run_projectionRawOutputLookupProgram_query
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    runNPOracleProgram projectionRawOutputLookupProgram
        (projectionRawOutputLookupBits n
          (projectionRunnerCallOutputs pcp input)
          (projectionQueryOffset
            (pcp.nativeWidth n) query.val bit.val))
        (projectionRawOutputLookupFuel
          (projectionRunnerCallOutputs pcp input)
          (projectionQueryOffset
            (pcp.nativeWidth n) query.val bit.val))
        (initialNPOracleState n
          (balancedLookupInput
            (projectionRunnerCallOutputs pcp input)
            (projectionQueryOffset
              (pcp.nativeWidth n) query.val bit.val))) =
      some
        (ProjectionRunnerCall.rawOutput pcp
          (.query (pcp.queryRequest input query bit))) := by
  have hindex :
      projectionQueryOffset (pcp.nativeWidth n) query.val bit.val <
        (projectionRunnerCallOutputs pcp input).length := by
    rw [projectionRunnerCallOutputs_length]
    exact (rowMajorOffset_lt query.isLt bit.isLt).trans_le
      (Nat.le_add_right _ _)
  have hvalue :
      (projectionRunnerCallOutputs pcp input)[
          projectionQueryOffset
            (pcp.nativeWidth n) query.val bit.val] =
        ProjectionRunnerCall.output pcp
          (.query (pcp.queryRequest input query bit)) := by
    have hget :=
      getD_projectionRunnerCallOutputs_query pcp input query bit
    rw [List.getD_eq_getElem _ _ hindex] at hget
    exact hget
  rw [run_projectionRawOutputLookupProgram n
    (projectionRunnerCallOutputs pcp input)
    (projectionQueryOffset (pcp.nativeWidth n) query.val bit.val)
    hindex]
  simp [hvalue, projectionRawOutput, ProjectionRunnerCall.output]

/-- The same fixed lookup reaches the exact published decision-runner payload
after the complete query rectangle. -/
theorem run_projectionRawOutputLookupProgram_decision
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode : ℕ)
    (hrandomnessCode :
      randomnessCode < 2 ^ pcp.nativeWidth n) :
    runNPOracleProgram projectionRawOutputLookupProgram
        (projectionRawOutputLookupBits n
          (projectionRunnerCallOutputs pcp input)
          (projectionDecisionOffset (pcp.nativeWidth n)
            (pcp.queryCount n) randomnessCode))
        (projectionRawOutputLookupFuel
          (projectionRunnerCallOutputs pcp input)
          (projectionDecisionOffset (pcp.nativeWidth n)
            (pcp.queryCount n) randomnessCode))
        (initialNPOracleState n
          (balancedLookupInput
            (projectionRunnerCallOutputs pcp input)
            (projectionDecisionOffset (pcp.nativeWidth n)
              (pcp.queryCount n) randomnessCode))) =
      some
        (ProjectionRunnerCall.rawOutput pcp
          (.decision (pcp.decisionRequest input fun bit =>
            randomnessCode.testBit bit.val))) := by
  have hindex :
      projectionDecisionOffset (pcp.nativeWidth n)
          (pcp.queryCount n) randomnessCode <
        (projectionRunnerCallOutputs pcp input).length := by
    rw [projectionRunnerCallOutputs_length]
    unfold projectionDecisionOffset
    omega
  have hvalue :
      (projectionRunnerCallOutputs pcp input)[
          projectionDecisionOffset (pcp.nativeWidth n)
            (pcp.queryCount n) randomnessCode] =
        ProjectionRunnerCall.output pcp
          (.decision (pcp.decisionRequest input fun bit =>
            randomnessCode.testBit bit.val)) := by
    have hget :=
      getD_projectionRunnerCallOutputs_decision pcp input
        randomnessCode hrandomnessCode
    rw [List.getD_eq_getElem _ _ hindex] at hget
    exact hget
  rw [run_projectionRawOutputLookupProgram n
    (projectionRunnerCallOutputs pcp input)
    (projectionDecisionOffset (pcp.nativeWidth n)
      (pcp.queryCount n) randomnessCode)
    hindex]
  simp [hvalue, projectionRawOutput, ProjectionRunnerCall.output]

/-- Decode one query-coordinate value from the actual balanced runner table. -/
def projectionTableQueryBit
    (outputs : List ℕ) (width : ℕ)
    (query bit : ℕ) : ProjectedRandomBit width :=
  decodeProjectedRandomBit width <|
    projectionRawOutput <|
      outputs.getD (projectionQueryOffset width query bit) 0

/-- Evaluate one complete projected address from decoded table coordinates. -/
def projectionTableAddress
    (outputs : List ℕ) (width query : ℕ)
    (randomness : BitInput width) : BitInput width :=
  fun bit =>
    (projectionTableQueryBit outputs width query bit.val).eval randomness

/-- Decode one decision row from the actual balanced runner table. -/
def projectionTableDecision
    (outputs : List ℕ) (width count randomnessCode : ℕ) :
    ThreeCNF count :=
  decodeThreeCNF count <|
    projectionRawOutput <|
      outputs.getD
        (projectionDecisionOffset width count randomnessCode) 0

@[simp] theorem projectionTableQueryBit_runnerOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    projectionTableQueryBit (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) query.val bit.val =
      pcp.queryAddressBits input query bit := by
  unfold projectionTableQueryBit projectionRawOutput
  rw [getD_projectionRunnerCallOutputs_query pcp input query bit]
  simp [ProjectionRunnerCall.output, ProjectionRunnerCall.rawOutput,
    ExecutableProjectionPCP.queryAddressBits]

@[simp] theorem projectionTableAddress_runnerOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n))
    (query : Fin (pcp.queryCount n)) :
    projectionTableAddress (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) query.val randomness =
      projectedInput pcp.toSemantic input randomness query := by
  funext bit
  change
    (projectionTableQueryBit (projectionRunnerCallOutputs pcp input)
      (pcp.nativeWidth n) query.val bit.val).eval randomness =
      (pcp.queryAddressBits input query bit).eval randomness
  rw [projectionTableQueryBit_runnerOutputs]

@[simp] theorem projectionTableDecision_runnerOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomnessCode : ℕ)
    (hrandomnessCode : randomnessCode < 2 ^ pcp.nativeWidth n) :
    projectionTableDecision (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) randomnessCode =
      pcp.decision input (fun bit =>
        randomnessCode.testBit bit.val) := by
  unfold projectionTableDecision projectionRawOutput
  rw [getD_projectionRunnerCallOutputs_decision pcp input
    randomnessCode hrandomnessCode]
  simp [ProjectionRunnerCall.output, ProjectionRunnerCall.rawOutput,
    ExecutableProjectionPCP.decision]

/-- The table interpretation recovers the exact semantic address list expected
by `compileUniversalOutputs`; this is the compiler's query-side handoff. -/
@[simp] theorem projectionTableAddresses_runnerOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (randomness : BitInput (pcp.nativeWidth n)) :
    List.ofFn (fun query : Fin (pcp.queryCount n) =>
      projectionTableAddress (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) query.val randomness) =
      projectedAddresses pcp.toSemantic input randomness := by
  unfold projectedAddresses
  apply congrArg List.ofFn
  funext query
  exact projectionTableAddress_runnerOutputs pcp input randomness query

end NearCubicWires.BoundedOracleStructuralProjectionTable

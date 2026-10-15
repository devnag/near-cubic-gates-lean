import Proof.MachineModel.PreserveRightProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Fixed heterogeneous projection-runner call

The structural recovery builder needs exactly two imported computations:
projection-address bits and verifier decision clauses.  This module gives them
one fixed tagged callee.  Each branch preserves its structural context beside
the imported result, so later node emission never reconstructs width, count,
or loop coordinates from an untyped host value.
-/

namespace NearCubicWires.ProjectionRunnerCallProgram

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

inductive ProjectionRunnerCall where
  | query (request : ProjectionQueryRequest)
  | decision (request : ProjectionDecisionRequest)

def ProjectionRunnerCall.inputLength : ProjectionRunnerCall → ℕ
  | .query request => request.inputArity
  | .decision request => request.inputArity

def ProjectionRunnerCall.requestCode : ProjectionRunnerCall → ℕ
  | .query request => request.code
  | .decision request => request.code

/-- Context retained after the imported call.  Query coordinates are repeated
deliberately: the runner consumes its native code while the structural emitter
receives a direct, canonical loop-coordinate payload. -/
def ProjectionRunnerCall.context : ProjectionRunnerCall → ℕ
  | .query request =>
      Nat.pair request.width <|
        Nat.pair request.count <|
          Nat.pair request.query.val request.bit.val
  | .decision request =>
      Nat.pair request.width request.count

def ProjectionRunnerCall.tag : ProjectionRunnerCall → ℕ
  | .query _ => 0
  | .decision _ => 1

def ProjectionRunnerCall.payload (call : ProjectionRunnerCall) : ℕ :=
  Nat.pair call.requestCode call.context

/-- Balanced-call atom: input length outside, then the heterogeneous tag and
the context-preserving source payload. -/
def ProjectionRunnerCall.atom (call : ProjectionRunnerCall) : ℕ :=
  Nat.pair call.inputLength (Nat.pair call.tag call.payload)

def ProjectionRunnerCall.sourceFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    ProjectionRunnerCall → ℕ
  | .query request => pcp.query.budget request
  | .decision request => pcp.decisionRunner.budget request

def ProjectionRunnerCall.rawOutput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    ProjectionRunnerCall → ℕ
  | .query request => pcp.query.execute request
  | .decision request => pcp.decisionRunner.execute request

def ProjectionRunnerCall.output
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (call : ProjectionRunnerCall) : ℕ :=
  Nat.pair (call.rawOutput pcp) call.context

def ProjectionRunnerCall.fuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (call : ProjectionRunnerCall) : ℕ :=
  taggedProgramChoiceFuel <| preserveRightFuel (call.sourceFuel pcp)

def ProjectionRunnerCall.requiredBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (call : ProjectionRunnerCall) : ℕ :=
  max
    (preserveRightBits (call.sourceFuel pcp) call.requestCode
      call.context (call.rawOutput pcp))
    (natBitLength call.atom)

/-- One fixed callee used by the public structural builder. -/
def projectionRunnerCallProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) : NPOracleProgram :=
  taggedProgramChoice
    (preserveRightProgram pcp.query.program)
    (preserveRightProgram pcp.decisionRunner.program)

theorem projectionRunnerCallProgram_oracleFree
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    OracleFree (projectionRunnerCallProgram pcp) := by
  exact taggedProgramChoice_oracleFree
    (preserveRightProgram pcp.query.program)
    (preserveRightProgram pcp.decisionRunner.program)
    (preserveRightProgram_oracleFree
      pcp.query.program pcp.queryOracleFree)
    (preserveRightProgram_oracleFree
      pcp.decisionRunner.program pcp.decisionOracleFree)

/-- Exact typed refinement for either imported runner.  The result and all
context fields come from the interpreter trace; the call atom carries no
semantic callback. -/
theorem run_projectionRunnerCallProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (call : ProjectionRunnerCall) :
    runNPOracleProgram (projectionRunnerCallProgram pcp)
        (call.requiredBits pcp) (call.fuel pcp)
        (initialNPOracleState call.inputLength
          (Nat.unpair call.atom).2) =
      some (call.output pcp) := by
  cases call with
  | query request =>
      let sourceBits := pcp.query.budget request
      let context :=
        Nat.pair request.width <|
          Nat.pair request.count <|
            Nat.pair request.query.val request.bit.val
      let rawOutput := pcp.query.execute request
      let wrapperBits :=
        preserveRightBits sourceBits request.code context rawOutput
      let maximumBits :=
        max wrapperBits <|
          natBitLength
            (Nat.pair request.inputArity
              (Nat.pair 0 (Nat.pair request.code context)))
      have hwrapper :
          runNPOracleProgram
              (preserveRightProgram pcp.query.program)
              wrapperBits (preserveRightFuel sourceBits)
              (initialNPOracleState request.inputArity
                (Nat.pair request.code context)) =
            some (Nat.pair rawOutput context) := by
        exact run_preserveRightProgram pcp.query.program
          request.inputArity sourceBits sourceBits request.code context
          rawOutput (pcp.query.run_eq_execute request)
      have hwrapperAtMaximum :
          runNPOracleProgram
              (preserveRightProgram pcp.query.program)
              maximumBits (preserveRightFuel sourceBits)
              (initialNPOracleState request.inputArity
                (Nat.pair request.code context)) =
            some (Nat.pair rawOutput context) :=
        run_bits_mono hwrapper (Nat.le_max_left _ _)
      have houtput :
          natBitLength (Nat.pair rawOutput context) ≤ maximumBits :=
        (run_output_bounded hwrapper).trans (Nat.le_max_left _ _)
      simpa only [projectionRunnerCallProgram,
        ProjectionRunnerCall.requiredBits, ProjectionRunnerCall.fuel,
        ProjectionRunnerCall.inputLength, ProjectionRunnerCall.atom,
        ProjectionRunnerCall.tag, ProjectionRunnerCall.payload,
        ProjectionRunnerCall.requestCode, ProjectionRunnerCall.context,
        ProjectionRunnerCall.sourceFuel, ProjectionRunnerCall.rawOutput,
        ProjectionRunnerCall.output, sourceBits, context, rawOutput,
        wrapperBits, maximumBits, Nat.unpair_pair] using
          run_taggedProgramChoice_zero
            (preserveRightProgram pcp.query.program)
            (preserveRightProgram pcp.decisionRunner.program)
            request.inputArity (Nat.pair request.code context)
            maximumBits (preserveRightFuel sourceBits)
            (Nat.pair rawOutput context)
            (Nat.le_max_right _ _)
            hwrapperAtMaximum houtput
  | decision request =>
      let sourceBits := pcp.decisionRunner.budget request
      let context := Nat.pair request.width request.count
      let rawOutput := pcp.decisionRunner.execute request
      let wrapperBits :=
        preserveRightBits sourceBits request.code context rawOutput
      let maximumBits :=
        max wrapperBits <|
          natBitLength
            (Nat.pair request.inputArity
              (Nat.pair 1 (Nat.pair request.code context)))
      have hwrapper :
          runNPOracleProgram
              (preserveRightProgram pcp.decisionRunner.program)
              wrapperBits (preserveRightFuel sourceBits)
              (initialNPOracleState request.inputArity
                (Nat.pair request.code context)) =
            some (Nat.pair rawOutput context) := by
        exact run_preserveRightProgram pcp.decisionRunner.program
          request.inputArity sourceBits sourceBits request.code context
          rawOutput (pcp.decisionRunner.run_eq_execute request)
      have hwrapperAtMaximum :
          runNPOracleProgram
              (preserveRightProgram pcp.decisionRunner.program)
              maximumBits (preserveRightFuel sourceBits)
              (initialNPOracleState request.inputArity
                (Nat.pair request.code context)) =
            some (Nat.pair rawOutput context) :=
        run_bits_mono hwrapper (Nat.le_max_left _ _)
      have houtput :
          natBitLength (Nat.pair rawOutput context) ≤ maximumBits :=
        (run_output_bounded hwrapper).trans (Nat.le_max_left _ _)
      simpa only [projectionRunnerCallProgram,
        ProjectionRunnerCall.requiredBits, ProjectionRunnerCall.fuel,
        ProjectionRunnerCall.inputLength, ProjectionRunnerCall.atom,
        ProjectionRunnerCall.tag, ProjectionRunnerCall.payload,
        ProjectionRunnerCall.requestCode, ProjectionRunnerCall.context,
        ProjectionRunnerCall.sourceFuel, ProjectionRunnerCall.rawOutput,
        ProjectionRunnerCall.output, sourceBits, context, rawOutput,
        wrapperBits, maximumBits, Nat.unpair_pair] using
          run_taggedProgramChoice_nonzero
            (preserveRightProgram pcp.query.program)
            (preserveRightProgram pcp.decisionRunner.program)
            request.inputArity 1 (Nat.pair request.code context)
            maximumBits (preserveRightFuel sourceBits)
            (Nat.pair rawOutput context)
            (by omega) (Nat.le_max_right _ _)
            hwrapperAtMaximum houtput

end NearCubicWires.ProjectionRunnerCallProgram

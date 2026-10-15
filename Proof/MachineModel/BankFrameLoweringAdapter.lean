import Proof.MachineModel.BankEmittedAtomLoop
import Proof.MachineModel.BankScheduleDiagonal
import Proof.MachineModel.PreserveRightProgram

/-!
# The frame-lowering adapter of the bank-framed emitter

`BankEmittedAtomLoop.inverseEmitterRuns_ofCompiler` consumes one stage between
the numeral bank's frame and the atom loop's own input frame:

`InverseFrameAdapterRuns` — started on
`publishedBankFrame outer pcppSource rate target code`, the stage must return

`pair (generatedBalancedRangeInput count context) (that same frame)`,

where `count` and `context` are the schedule's structural atom count and public
request context at `target`.

Two things are bundled there, and this module separates them.

* **Frame retention.**  The bank's frame is both the stage's input and the
  point code the atom loop carries beside its generated range.  §1–§3 discharge
  that half outright: the adapter is the frame duplicator followed by the
  shape stage run under `PreserveRightProgram.preserveRightProgram`, so the
  retained copy is never touched by the arithmetic.  Nothing about the shape
  stage is used except its own run.
* **The atom shape.**  What remains is `InverseAtomShapeRuns` (§3): from the
  bank's frame, produce `generatedBalancedRangeInput count context`.  This is
  the projection-runner table together with the compiled formula length, and it
  is the one residual of the adapter.

§4 records exactly what that residual has to compute, and which half of it the
tree already executes.  Two points are worth stating explicitly because they
constrain any construction.

1. The context is *pure pairing* over the runner table and three numerals
   (`inverseAtomContext_eq`), and the table's balanced encoding is literally the
   left component of `ProjectionRunnerBalancedProgram`'s output
   (`run_inverseProjectionRunnerBalancedProgram`).  The formula length is not
   pairing: it counts the compiled nodes of every decision row, so it reads the
   table's contents and not only the shape numerals.
2. The available table run is stated at the *PCP input's* public length
   `inverseScheduleLength …`, while the adapter runs at the request's public
   length `target`.  Those coincide exactly on the schedule's diagonal.  The
   identification is **not** asserted here: `BankScheduleDiagonal` records that
   the consumer of `bodyRun` does not pin `target` to a scheduled source length,
   so a construction of `InverseAtomShapeRuns` must either carry the diagonal
   hypothesis explicitly or produce the scheduled numerals off the diagonal as
   well.  §4 threads the identification as a hypothesis of the one lemma that
   needs it.
-/

namespace NearCubicWires.BankFrameLoweringAdapter

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The frame duplicator -/

/-- Duplicate the frame in front of itself.  This is the whole of the adapter's
frame bookkeeping: the left copy is lowered to the loop's input frame and the
right copy is the retained point code. -/
private def frameDuplicateProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] private theorem frameDuplicateProgram_oracleFree :
    OracleFree frameDuplicateProgram := by
  rfl

private def frameDuplicateBits (frame : ℕ) : ℕ :=
  natBitLength (Nat.pair frame frame)

private theorem run_frameDuplicateProgram (inputLength frame : ℕ) :
    runNPOracleProgram frameDuplicateProgram (frameDuplicateBits frame) 2
        (initialNPOracleState inputLength frame) =
      some (Nat.pair frame frame) := by
  have hbits : natBitLength (Nat.pair frame frame) ≤ frameDuplicateBits frame :=
    le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair frame frame) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-! ## 2. The adapter and its resource envelopes -/

/-- **The frame-lowering adapter.**  One fixed stream: duplicate the bank's
frame, then run the atom-shape stage on the left copy while the right copy is
preserved verbatim. -/
def inverseFrameAdapterProgram (shape : NPOracleProgram) : NPOracleProgram :=
  linkPrograms frameDuplicateProgram (preserveRightProgram shape)

theorem inverseFrameAdapterProgram_oracleFree {shape : NPOracleProgram}
    (hshape : OracleFree shape) :
    OracleFree (inverseFrameAdapterProgram shape) :=
  oracleFree_linkPrograms frameDuplicateProgram_oracleFree
    (preserveRightProgram_oracleFree shape hshape)

/-- The bank's frame at one request. -/
noncomputable def inverseAdapterFrame
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (LanguageEvaluationRequest.length request)
    (LanguageEvaluationRequest.code request)

/-- The loop's input frame at one request. -/
noncomputable def inverseAdapterRange
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : LanguageEvaluationRequest) : ℕ :=
  generatedBalancedRangeInput
    (inverseAtomCount contracts clockDepth machine advantageExponent pcp
      (LanguageEvaluationRequest.length request))
    (inverseAtomContext contracts clockDepth machine advantageExponent pcp
      (LanguageEvaluationRequest.length request))

noncomputable def inverseFrameAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shapeBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (frameDuplicateBits
      (inverseAdapterFrame contracts clockDepth advantageExponent request))
    (preserveRightBits (shapeBits request)
      (inverseAdapterFrame contracts clockDepth advantageExponent request)
      (inverseAdapterFrame contracts clockDepth advantageExponent request)
      (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
        request))

def inverseFrameAdapterFuel (shape : NPOracleProgram)
    (shapeFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel (preserveRightProgram shape) 2 (preserveRightFuel (shapeFuel request))

/-! ## 3. The frame retention, discharged -/

/-- **The adapter's one residual.**  Started on the numeral bank's frame, the
atom-shape stage returns the atom loop's generated-range input at that target:
the schedule's structural atom count paired with its public request context.
Nothing about the frame is asked of it — the adapter retains the frame itself. -/
def InverseAtomShapeRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram shape (shapeBits ⟨target, input⟩)
        (shapeFuel ⟨target, input⟩)
        (initialNPOracleState target
          (inverseAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
          ⟨target, input⟩)

/-- **The frame-lowering premise, from the atom-shape stage alone.**  The frame
retention of `BankEmittedAtomLoop.InverseFrameAdapterRuns` is discharged: no
hypothesis about the bank's frame, the schedule, or the diagonal is used, and
the only statement left about the adapter is the atom shape it computes. -/
theorem inverseFrameAdapterRuns_ofShape
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ)
    (hshape :
      InverseAtomShapeRuns contracts clockDepth machine advantageExponent pcp
        shape shapeBits shapeFuel) :
    InverseFrameAdapterRuns contracts clockDepth machine advantageExponent pcp
      (inverseFrameAdapterProgram shape)
      (inverseFrameAdapterBits contracts clockDepth machine advantageExponent
        pcp shapeBits)
      (inverseFrameAdapterFuel shape shapeFuel) := by
  intro target hlarge input
  exact run_occurrenceStage
    (run_frameDuplicateProgram target
      (inverseAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩))
    (run_preserveRightProgram shape target (shapeBits ⟨target, input⟩)
      (shapeFuel ⟨target, input⟩)
      (inverseAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩)
      (inverseAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩)
      (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
        ⟨target, input⟩)
      (hshape target hlarge input))

/-! ## 4. What the atom-shape stage has to compute -/

/-- The public request context of the loop is pure pairing over the
projection-runner table and the three shape numerals. -/
theorem inverseAtomContext_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target =
      Nat.pair
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)))
        (Nat.pair
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (Nat.pair
            (pcp.queryCount
              (inverseScheduleLength contracts clockDepth advantageExponent
                target))
            (inverseScheduleBound contracts clockDepth advantageExponent
              target))) :=
  rfl

/-- The generated range's count is the compiled formula length of the same
table: unlike the context it reads the table's contents, not only its shape. -/
theorem inverseAtomCount_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    inverseAtomCount contracts clockDepth machine advantageExponent pcp target =
      BoundedOracleStructuralFormulaTable.tableBoundedOracleStructuralFormulaLength
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target) :=
  rfl

/-- **The table half of the shape stage, already executed.**  The published
balanced projection-runner pipeline returns the schedule's runner table in the
exact balanced encoding the context pairs, beside the runner range's own
context.  The run is stated at the *PCP input's* public length; the adapter runs
at the request's public length, so a construction of `InverseAtomShapeRuns` must
supply the identification of the two — see `BankScheduleDiagonal`. -/
theorem run_inverseProjectionRunnerBalancedProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    runNPOracleProgram (projectionRunnerBalancedProgram pcp)
        (projectionRunnerBalancedBits pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (projectionRunnerBalancedFuel pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (initialNPOracleState
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (projectionRunnerBalancedInput pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))) =
      some
        (Nat.pair
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)))
          (projectionRunnerRangeContext pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))) :=
  run_projectionRunnerBalancedProgram pcp
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)

/-- **The diagonal, threaded.**  On a request whose public length is the
schedule's own source length the two public lengths of §4 coincide, so the
executed table run above is a run at the adapter's own public length.  The
identification is supplied as a hypothesis, never asserted: `BankScheduleDiagonal`
records that the consumer of `bodyRun` does not pin the request's public length
to a scheduled source length. -/
theorem run_inverseProjectionRunnerBalancedProgram_atLength
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target inputLength : ℕ)
    (hdiagonal :
      inputLength =
        inverseScheduleLength contracts clockDepth advantageExponent target) :
    runNPOracleProgram (projectionRunnerBalancedProgram pcp)
        (projectionRunnerBalancedBits pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (projectionRunnerBalancedFuel pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (initialNPOracleState inputLength
          (projectionRunnerBalancedInput pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))) =
      some
        (Nat.pair
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)))
          (projectionRunnerRangeContext pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))) := by
  refine Eq.trans (congrArg
    (fun length =>
      runNPOracleProgram (projectionRunnerBalancedProgram pcp)
        (projectionRunnerBalancedBits pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (projectionRunnerBalancedFuel pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (initialNPOracleState length
          (projectionRunnerBalancedInput pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)))) hdiagonal) ?_
  exact run_inverseProjectionRunnerBalancedProgram contracts clockDepth machine
    advantageExponent pcp target

end NearCubicWires.BankFrameLoweringAdapter

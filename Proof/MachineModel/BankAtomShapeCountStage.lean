import Proof.MachineModel.BankFrameLoweringAdapter

/-!
# The atom-shape stage's count half, executed

`BankFrameLoweringAdapter.inverseFrameAdapterRuns_ofShape` leaves exactly one
residual, `InverseAtomShapeRuns`: from the numeral bank's frame produce

`generatedBalancedRangeInput count context`,

and §4 of that module warns that — unlike the context, which is pure pairing —
the count is `tableBoundedOracleStructuralFormulaLength`, which reads the
runner table's *contents* and not only its shape numerals.

## The count is already executed

It is, and by a program this fleet already ships.
`BoundedOracleStructuralSelectiveProgram.structuralFormulaProgram` returns
`structuralFormulaResponseCode = pair length atom` — the formula *length* beside
the atom — and `StructuralAtomCalleeProgram.structuralAtomTakeRightProgram`
throws the length away because the emitter loop wants the atom.  Projecting the
other component instead computes the count, at the same one premise
(`StructuralCompilerRunsAt`) and with no new obligation class: the length
component does not depend on the requested index, so index `0` serves, and
`0 < inverseAtomCount` holds unconditionally because the length is a successor.

§1–§2 build that projection.  §3–§4 assemble the count in front of the context

`context ↦ pair count context = generatedBalancedRangeInput count context`

as one reusable stage.  §5 discharges `InverseAtomShapeRuns` from it: what is
left is `InverseAtomContextRuns`, the *context* half alone — the projection
runner's balanced table paired with the bank's own width, query-count and
size-cap registers, and nothing that reads the table's contents.

## What this does not do

The count premise is `InverseCompilerRuns` at index `0`, i.e. literally the
premise `BankEmittedAtomLoop.inverse_bodyRun_ofCompiler` already carries, so no
hypothesis is added.  The diagonal is untouched: neither §4 nor §5 mentions a
schedule length, so the schedule-diagonal identification remains confined to the
context half, exactly where `BankFrameLoweringAdapter` §4 located it.
-/

namespace NearCubicWires.BankAtomShapeCountStage

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
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
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

private theorem natBitLength_mono' {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-! ## 1. The other response projection -/

/-- The pointwise runner returns `pair length atom`; the count stage keeps the
length.  This is the mirror of
`StructuralAtomCalleeProgram.structuralAtomTakeRightProgram`. -/
def structuralAtomTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] theorem structuralAtomTakeLeftProgram_oracleFree :
    OracleFree structuralAtomTakeLeftProgram := by
  rfl

theorem run_structuralAtomTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleft : natBitLength left ≤ maximumBits) :
    runNPOracleProgram structuralAtomTakeLeftProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft

/-! ## 2. The compiled formula length, executed -/

def structuralAtomCountProgram : NPOracleProgram :=
  linkPrograms structuralFormulaProgram structuralAtomTakeLeftProgram

theorem structuralAtomCountProgram_oracleFree :
    OracleFree structuralAtomCountProgram :=
  oracleFree_linkPrograms structuralFormulaProgram_oracleFree
    structuralAtomTakeLeftProgram_oracleFree

def structuralAtomCountBits (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits : ℕ) : ℕ :=
  occurrenceStageBits machineInputLength
    (structuralFormulaPipelineBits machineInputLength outputs width count bound
      index compilerBits)
    (natBitLength
      (structuralFormulaResponseCode outputs width count bound index))

def structuralAtomCountFuel (outputs : List ℕ)
    (width count bound index compilerFuel : ℕ) : ℕ :=
  linkFuel structuralAtomTakeLeftProgram
    (structuralFormulaPipelineFuel outputs width count bound index compilerFuel)
    2

/-- **The count, executed.**  From the same generated request body the callee
of `StructuralAtomCalleeProgram` consumes, the fixed stream returns the
compiled formula length of the table, modulo the one run of the nested
compiler. -/
theorem run_structuralAtomCountProgram
    (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits compilerFuel : ℕ)
    (hcompiler :
      runNPOracleProgram selectiveCountCasesProgram compilerBits compilerFuel
          (initialNPOracleState machineInputLength <|
            structuralCompilerCoreInput outputs width count bound index) =
        some
          (selectiveWireCode
            (selectiveCompileTableBoundedOracleVerifier outputs width count
              bound (index - descriptionWidth width bound)))) :
    runNPOracleProgram structuralAtomCountProgram
        (structuralAtomCountBits machineInputLength outputs width count bound
          index compilerBits)
        (structuralAtomCountFuel outputs width count bound index compilerFuel)
        (initialNPOracleState machineInputLength
          (structuralFormulaRequestCode outputs width count bound index)) =
      some
        (tableBoundedOracleStructuralFormulaLength outputs width count bound) := by
  refine run_occurrenceStage
    (run_structuralFormulaProgram_of_compiler_run machineInputLength outputs
      width count bound index compilerBits compilerFuel hcompiler) ?_
  exact run_structuralAtomTakeLeftProgram machineInputLength
    (tableBoundedOracleStructuralFormulaLength outputs width count bound)
    (tableBoundedOracleStructuralFormulaAtomAt outputs width count bound index)
    (natBitLength_mono' (Nat.left_le_pair _ _))

/-- **The count at an executable projection PCP.**  The premise is
`StructuralAtomCalleeProgram.StructuralCompilerRunsAt` at the single index `0`
— the same premise class the atom loop already carries at every index. -/
theorem run_structuralAtomCountProgram_index
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (machineInputLength bound compilerBits compilerFuel : ℕ)
    (hcompiler :
      StructuralCompilerRunsAt pcp input machineInputLength bound 0 compilerBits
        compilerFuel) :
    runNPOracleProgram structuralAtomCountProgram
        (structuralAtomCountBits machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound 0 compilerBits)
        (structuralAtomCountFuel (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) bound 0 compilerFuel)
        (initialNPOracleState machineInputLength
          (Nat.pair 0 (structuralAtomContext pcp input bound))) =
      some (structuralAtomCount pcp input bound) :=
  run_structuralAtomCountProgram machineInputLength
    (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
    (pcp.queryCount n) bound 0 compilerBits compilerFuel hcompiler

/-! ## 3. The request frame of the count stage -/

/-- Build the count stage's request beside a retained copy of the context:
`context ↦ pair (pair 0 context) context`. -/
private def atomContextRequestProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .pair 2 0 3 2
  , .pair 3 0 0 3
  , .halt 0
  ]

@[simp] private theorem atomContextRequestProgram_oracleFree :
    OracleFree atomContextRequestProgram := by
  rfl

private def atomContextRequestBits (context : ℕ) : ℕ :=
  natBitLength (Nat.pair (Nat.pair 0 context) context)

private theorem run_atomContextRequestProgram (inputLength context : ℕ) :
    runNPOracleProgram atomContextRequestProgram
        (atomContextRequestBits context) 4
        (initialNPOracleState inputLength context) =
      some (Nat.pair (Nat.pair 0 context) context) := by
  have hfinal : natBitLength (Nat.pair (Nat.pair 0 context) context) ≤
      atomContextRequestBits context := le_refl _
  have hrequest : natBitLength (Nat.pair 0 context) ≤
      atomContextRequestBits context :=
    natBitLength_mono' (Nat.left_le_pair _ _)
  have hzero : natBitLength 0 ≤ atomContextRequestBits context :=
    natBitLength_mono' (Nat.zero_le _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (by rfl) rfl hzero]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 0 context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hrequest]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair 0 context) context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hfinal]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfinal

/-! ## 4. The count installed in front of the context -/

/-- **The reusable count-and-pair stage.**  One fixed stream taking the shared
public request context to the atom loop's own input frame. -/
def atomShapeCountProgram : NPOracleProgram :=
  linkPrograms atomContextRequestProgram
    (preserveRightProgram structuralAtomCountProgram)

theorem atomShapeCountProgram_oracleFree : OracleFree atomShapeCountProgram :=
  oracleFree_linkPrograms atomContextRequestProgram_oracleFree
    (preserveRightProgram_oracleFree structuralAtomCountProgram
      structuralAtomCountProgram_oracleFree)

def atomShapeCountBits (machineInputLength context countBits count : ℕ) : ℕ :=
  occurrenceStageBits machineInputLength (atomContextRequestBits context)
    (preserveRightBits countBits (Nat.pair 0 context) context count)

def atomShapeCountFuel (countFuel : ℕ) : ℕ :=
  linkFuel (preserveRightProgram structuralAtomCountProgram) 4
    (preserveRightFuel countFuel)

theorem run_atomShapeCountProgram
    (machineInputLength context countBits countFuel count : ℕ)
    (hcount :
      runNPOracleProgram structuralAtomCountProgram countBits countFuel
          (initialNPOracleState machineInputLength (Nat.pair 0 context)) =
        some count) :
    runNPOracleProgram atomShapeCountProgram
        (atomShapeCountBits machineInputLength context countBits count)
        (atomShapeCountFuel countFuel)
        (initialNPOracleState machineInputLength context) =
      some (generatedBalancedRangeInput count context) :=
  run_occurrenceStage
    (run_atomContextRequestProgram machineInputLength context)
    (run_preserveRightProgram structuralAtomCountProgram machineInputLength
      countBits countFuel (Nat.pair 0 context) context count hcount)

/-! ## 5. `InverseAtomShapeRuns` from the context half alone -/

/-- **The context half of the atom-shape stage.**  From the numeral bank's
frame produce the shared public request context of the loop — the runner
table's balanced encoding paired with the scheduled width, query count and
size cap.  Nothing here reads the table's contents. -/
def InverseAtomContextRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram context (contextBits ⟨target, input⟩)
        (contextFuel ⟨target, input⟩)
        (initialNPOracleState target
          (inverseAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)

/-- **The atom-shape stage.**  The context half, then the count-and-pair
stage. -/
def inverseAtomShapeProgram (context : NPOracleProgram) : NPOracleProgram :=
  linkPrograms context atomShapeCountProgram

theorem inverseAtomShapeProgram_oracleFree {context : NPOracleProgram}
    (hcontext : OracleFree context) :
    OracleFree (inverseAtomShapeProgram context) :=
  oracleFree_linkPrograms hcontext atomShapeCountProgram_oracleFree

noncomputable def inverseAtomShapeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (contextBits : LanguageEvaluationRequest → ℕ) (compilerBits : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (contextBits request)
    (atomShapeCountBits (LanguageEvaluationRequest.length request)
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (structuralAtomCountBits (LanguageEvaluationRequest.length request)
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (inverseScheduleBound contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request))
        0
        (compilerBits (LanguageEvaluationRequest.length request) 0))
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request)))

noncomputable def inverseAtomShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (contextFuel : LanguageEvaluationRequest → ℕ) (compilerFuel : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel atomShapeCountProgram (contextFuel request)
    (atomShapeCountFuel
      (structuralAtomCountFuel
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request)))
        (inverseScheduleBound contracts clockDepth advantageExponent
          (LanguageEvaluationRequest.length request))
        0
        (compilerFuel (LanguageEvaluationRequest.length request) 0)))

/-- The atom count is a successor, so index `0` is always in range. -/
theorem inverseAtomCount_pos
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    0 < inverseAtomCount contracts clockDepth machine advantageExponent pcp
      target := by
  simp only [inverseAtomCount, structuralAtomCount,
    tableBoundedOracleStructuralFormulaLength]
  omega

/-- **The adapter's residual, halved.**  `InverseAtomShapeRuns` follows from
the context half alone: the count is executed by §2–§4 under the compiler
premise the atom loop already carries, at the single index `0`. -/
theorem inverseAtomShapeRuns_ofContext
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcontext :
      InverseAtomContextRuns contracts clockDepth machine advantageExponent pcp
        context contextBits contextFuel)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseAtomShapeRuns contracts clockDepth machine advantageExponent pcp
      (inverseAtomShapeProgram context)
      (inverseAtomShapeBits contracts clockDepth machine advantageExponent pcp
        contextBits compilerBits)
      (inverseAtomShapeFuel contracts clockDepth machine advantageExponent pcp
        contextFuel compilerFuel) := by
  intro target hlarge input
  exact run_occurrenceStage (hcontext target hlarge input)
    (run_atomShapeCountProgram target
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target)
      _ _
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target)
      (run_structuralAtomCountProgram_index pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target)
        target (inverseScheduleBound contracts clockDepth advantageExponent
          target)
        (compilerBits target 0) (compilerFuel target 0)
        (hcompiler target 0
          (inverseAtomCount_pos contracts clockDepth machine advantageExponent
            pcp target))))

end NearCubicWires.BankAtomShapeCountStage

import Proof.MachineModel.BankDiagonalBodyClosure
import Proof.Circuits.FixedScheduleAtomLoop

/-!
# The fixed schedule's diagonal cluster, assembled

The fixed twin of `BankDiagonalBodyClosure`.  `FixedScheduleAtomLoop.fixed_bodyRun_ofPresentation`
consumes eleven named premises; three of them belong to the numeral bank and the
schedule's diagonal.  This module replaces all three by statements from which the
bank has been removed, exactly as the inverse cluster does:

* `FixedAtomTableRuns` — the projection runner's balanced table at the bank's
  frame;
* `FixedCaseOnePointRuns` / `FixedCaseTwoPointRuns` — the two chains at the
  requested point code, the bank frame projected away unconditionally.

## What is generic and is therefore *not* replayed

Every program and every frame lemma on this cluster is schedule free and is
cited from the inverse modules unchanged: `BankFrameLoweringAdapter.inverseFrameAdapterProgram`
and `…Fuel`, `BankAtomShapeCountStage.atomShapeCountProgram`/`…Bits`/`…Fuel` with
`run_atomShapeCountProgram`, `BankAtomContextRegisters.inverseAtomContextProgram`,
`bankShapeNumeralProgram`/`bankShapeNumerals` with `run_bankShapeNumeralProgram`,
`BankAtomContextRegisters.inverseBankWidth`/`inverseBankQueryCount` (both are
functions of the request's *public length* alone, with no schedule in them), and
`BankFramedTargetChains.bankFramedChainProgram`/`bankFramedChainFuel` with
`run_bankFramedChainProgram`.  `BankScheduleDiagonal.sourceIndexOfLength_of_eq_sourceLength`
and `bankSourceLength_of_eq_sourceLength` are index generic and are reused.

## The diagonal on this schedule

`hdiagonal` is still required — the fixed schedule is not length uniform — but
its statement is one function application shorter than the inverse one, because
the fixed chain's index is `CaseOneRecoveryAssembly.fixedSelectedSource` itself
with no `RecoveryScheduleEnvelope.inverseSourceIndex` in front of it.
-/

namespace NearCubicWires.FixedScheduleDiagonalClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private frameDuplicateBits run_frameDuplicateProgram from
  Proof.MachineModel.BankFrameLoweringAdapter

open private contextDuplicateBits run_contextDuplicateProgram contextSwapProgram
  contextSwapBits run_contextSwapProgram from Proof.MachineModel.BankAtomContextRegisters

/-! ## 1. The frame-lowering adapter at the fixed bank -/

/-- The bank's frame at one request. -/
noncomputable def fixedAdapterFrame
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (fixedBankRate contracts requestedRate)
    (LanguageEvaluationRequest.length request)
    (LanguageEvaluationRequest.code request)

/-- The loop's input frame at one request. -/
noncomputable def fixedAdapterRange
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : LanguageEvaluationRequest) : ℕ :=
  generatedBalancedRangeInput
    (fixedAtomCount contracts clockDepth machine requestedRate pcp
      (LanguageEvaluationRequest.length request))
    (fixedAtomContext contracts clockDepth machine requestedRate pcp
      (LanguageEvaluationRequest.length request))

noncomputable def fixedFrameAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shapeBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (frameDuplicateBits
      (fixedAdapterFrame contracts clockDepth requestedRate request))
    (preserveRightBits (shapeBits request)
      (fixedAdapterFrame contracts clockDepth requestedRate request)
      (fixedAdapterFrame contracts clockDepth requestedRate request)
      (fixedAdapterRange contracts clockDepth machine requestedRate pcp
        request))

/-- **The adapter's one residual.**  Started on the numeral bank's frame, the
atom-shape stage returns the atom loop's generated-range input at that target. -/
def FixedAtomShapeRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (input : BitInput target),
    runNPOracleProgram shape (shapeBits ⟨target, input⟩)
        (shapeFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (fixedAdapterRange contracts clockDepth machine requestedRate pcp
          ⟨target, input⟩)

/-- **The frame-lowering premise, from the atom-shape stage alone.**  The fixed
twin of `BankFrameLoweringAdapter.inverseFrameAdapterRuns_ofShape`. -/
theorem fixedFrameAdapterRuns_ofShape
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ)
    (hshape :
      FixedAtomShapeRuns contracts clockDepth machine requestedRate pcp shape
        shapeBits shapeFuel) :
    FixedFrameAdapterRuns contracts clockDepth machine requestedRate pcp
      (inverseFrameAdapterProgram shape)
      (fixedFrameAdapterBits contracts clockDepth machine requestedRate pcp
        shapeBits)
      (inverseFrameAdapterFuel shape shapeFuel) := by
  intro target hlarge input
  exact run_occurrenceStage
    (run_frameDuplicateProgram target
      (fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩))
    (run_preserveRightProgram shape target (shapeBits ⟨target, input⟩)
      (shapeFuel ⟨target, input⟩)
      (fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩)
      (fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩)
      (fixedAdapterRange contracts clockDepth machine requestedRate pcp
        ⟨target, input⟩)
      (hshape target hlarge input))

/-! ## 2. What the atom-shape stage has to compute -/

/-- The public request context of the loop is pure pairing over the
projection-runner table and the three shape numerals. -/
theorem fixedAtomContext_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    fixedAtomContext contracts clockDepth machine requestedRate pcp target =
      Nat.pair
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target)))
        (Nat.pair
          (pcp.nativeWidth
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (Nat.pair
            (pcp.queryCount
              (fixedScheduleLength contracts clockDepth requestedRate target))
            (fixedScheduleBound contracts clockDepth requestedRate target))) :=
  rfl

/-- The generated range's count is the compiled formula length of the same
table. -/
theorem fixedAtomCount_eq
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    fixedAtomCount contracts clockDepth machine requestedRate pcp target =
      BoundedOracleStructuralFormulaTable.tableBoundedOracleStructuralFormulaLength
        (projectionRunnerCallOutputs pcp
          (fixedScheduleInput contracts clockDepth machine requestedRate
            target))
        (pcp.nativeWidth
          (fixedScheduleLength contracts clockDepth requestedRate target))
        (pcp.queryCount
          (fixedScheduleLength contracts clockDepth requestedRate target))
        (fixedScheduleBound contracts clockDepth requestedRate target) :=
  rfl

/-! ## 3. The atom-shape stage from the context half alone -/

/-- **The context half of the atom-shape stage.** -/
def FixedAtomContextRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (input : BitInput target),
    runNPOracleProgram context (contextBits ⟨target, input⟩)
        (contextFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (fixedAtomContext contracts clockDepth machine requestedRate pcp target)

noncomputable def fixedAtomShapeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (contextBits : LanguageEvaluationRequest → ℕ) (compilerBits : ℕ → ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (contextBits request)
    (atomShapeCountBits (LanguageEvaluationRequest.length request)
      (fixedAtomContext contracts clockDepth machine requestedRate pcp
        (LanguageEvaluationRequest.length request))
      (structuralAtomCountBits (LanguageEvaluationRequest.length request)
        (projectionRunnerCallOutputs pcp
          (fixedScheduleInput contracts clockDepth machine requestedRate
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request)))
        (fixedScheduleBound contracts clockDepth requestedRate
          (LanguageEvaluationRequest.length request))
        0
        (compilerBits (LanguageEvaluationRequest.length request) 0))
      (fixedAtomCount contracts clockDepth machine requestedRate pcp
        (LanguageEvaluationRequest.length request)))

noncomputable def fixedAtomShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
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
          (fixedScheduleInput contracts clockDepth machine requestedRate
            (LanguageEvaluationRequest.length request)))
        (pcp.nativeWidth
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request)))
        (pcp.queryCount
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request)))
        (fixedScheduleBound contracts clockDepth requestedRate
          (LanguageEvaluationRequest.length request))
        0
        (compilerFuel (LanguageEvaluationRequest.length request) 0)))

/-- The atom count is a successor, so index `0` is always in range. -/
theorem fixedAtomCount_pos
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    0 < fixedAtomCount contracts clockDepth machine requestedRate pcp target := by
  simp only [fixedAtomCount, structuralAtomCount,
    tableBoundedOracleStructuralFormulaLength]
  omega

/-- **The adapter's residual, halved.**  The fixed twin of
`BankAtomShapeCountStage.inverseAtomShapeRuns_ofContext`. -/
theorem fixedAtomShapeRuns_ofContext
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcontext :
      FixedAtomContextRuns contracts clockDepth machine requestedRate pcp
        context contextBits contextFuel)
    (hcompiler :
      FixedCompilerRuns contracts clockDepth machine requestedRate pcp
        compilerBits compilerFuel) :
    FixedAtomShapeRuns contracts clockDepth machine requestedRate pcp
      (inverseAtomShapeProgram context)
      (fixedAtomShapeBits contracts clockDepth machine requestedRate pcp
        contextBits compilerBits)
      (fixedAtomShapeFuel contracts clockDepth machine requestedRate pcp
        contextFuel compilerFuel) := by
  intro target hlarge input
  exact run_occurrenceStage (hcontext target hlarge input)
    (run_atomShapeCountProgram target
      (fixedAtomContext contracts clockDepth machine requestedRate pcp target)
      _ _
      (fixedAtomCount contracts clockDepth machine requestedRate pcp target)
      (run_structuralAtomCountProgram_index pcp
        (fixedScheduleInput contracts clockDepth machine requestedRate target)
        target (fixedScheduleBound contracts clockDepth requestedRate target)
        (compilerBits target 0) (compilerFuel target 0)
        (hcompiler target 0
          (fixedAtomCount_pos contracts clockDepth machine requestedRate pcp
            target))))

/-! ## 4. The context, from the table stage alone -/

/-- **The adapter's last residual.** -/
def FixedAtomTableRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (input : BitInput target),
    runNPOracleProgram table (tableBits ⟨target, input⟩)
        (tableFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target)))

/-- **The join fact at the fixed schedule.**  On the schedule's diagonal, and
for a presented PCP, the loop's public request context is the projection-runner
table paired with the bank's *own* width and query-count registers and the size
cap computed from the width register.  The bank registers are schedule free, so
`BankAtomContextRegisters.inverseBankWidth`/`inverseBankQueryCount` are the
fixed side's registers too. -/
theorem fixedAtomContext_ofRegisters
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target : ℕ)
    (hdiagonal :
      target = fixedScheduleLength contracts clockDepth requestedRate target) :
    Nat.pair
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target)))
        (bankShapeNumerals
          (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
            (inverseBankWidth contracts clockDepth target))
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)) =
      fixedAtomContext contracts clockDepth machine requestedRate pcp target := by
  have hindex :
      sourceIndexOfLength target =
        fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          target :=
    sourceIndexOfLength_of_eq_sourceLength hdiagonal
  have hlength :
      bankSourceLength target =
        fixedScheduleLength contracts clockDepth requestedRate target :=
    bankSourceLength_of_eq_sourceLength hdiagonal
  have hwidth :
      inverseBankWidth contracts clockDepth target =
        pcp.nativeWidth
          (fixedScheduleLength contracts clockDepth requestedRate target) := by
    rw [inverseBankWidth, hindex]
    exact (presentsPaddedOuterPCP_scheduledWidth hpresentation _).symm
  have hquery :
      inverseBankQueryCount contracts clockDepth target =
        pcp.queryCount
          (fixedScheduleLength contracts clockDepth requestedRate target) := by
    rw [inverseBankQueryCount, hlength]
    exact (congrFun (presentsPaddedOuterPCP_queryCount hpresentation) _).symm
  have hbound :
      oracleSizeBound (fixedRequiredDegree contracts requestedRate)
          (inverseBankWidth contracts clockDepth target) =
        fixedScheduleBound contracts clockDepth requestedRate target := by
    rw [inverseBankWidth, hindex]
    rfl
  rw [fixedAtomContext_eq, bankShapeNumerals, hbound, hwidth, hquery]

/-- Width of the context stage at one request. -/
noncomputable def fixedAtomContextBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (contextDuplicateBits
      (fixedAdapterFrame contracts clockDepth requestedRate request))
    (occurrenceStageBits (LanguageEvaluationRequest.length request)
      (preserveRightBits
        (bankShapeNumeralBits (fixedRequiredDegree contracts requestedRate)
          (LanguageEvaluationRequest.length request)
          (bankSourceLength (LanguageEvaluationRequest.length request))
          (inverseBankWidth contracts clockDepth
            (LanguageEvaluationRequest.length request))
          (inverseBankQueryCount contracts clockDepth
            (LanguageEvaluationRequest.length request))
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate)
            (sourceIndexOfLength (LanguageEvaluationRequest.length request)))
          (LanguageEvaluationRequest.code request))
        (fixedAdapterFrame contracts clockDepth requestedRate request)
        (fixedAdapterFrame contracts clockDepth requestedRate request)
        (bankShapeNumerals
          (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
            (inverseBankWidth contracts clockDepth
              (LanguageEvaluationRequest.length request)))
          (inverseBankWidth contracts clockDepth
            (LanguageEvaluationRequest.length request))
          (inverseBankQueryCount contracts clockDepth
            (LanguageEvaluationRequest.length request))))
      (occurrenceStageBits (LanguageEvaluationRequest.length request)
        (contextSwapBits
          (bankShapeNumerals
            (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
              (inverseBankWidth contracts clockDepth
                (LanguageEvaluationRequest.length request)))
            (inverseBankWidth contracts clockDepth
              (LanguageEvaluationRequest.length request))
            (inverseBankQueryCount contracts clockDepth
              (LanguageEvaluationRequest.length request)))
          (fixedAdapterFrame contracts clockDepth requestedRate request))
        (preserveRightBits (tableBits request)
          (fixedAdapterFrame contracts clockDepth requestedRate request)
          (bankShapeNumerals
            (oracleSizeBound (fixedRequiredDegree contracts requestedRate)
              (inverseBankWidth contracts clockDepth
                (LanguageEvaluationRequest.length request)))
            (inverseBankWidth contracts clockDepth
              (LanguageEvaluationRequest.length request))
            (inverseBankQueryCount contracts clockDepth
              (LanguageEvaluationRequest.length request)))
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (fixedScheduleInput contracts clockDepth machine requestedRate
                (LanguageEvaluationRequest.length request)))))))

/-- Fuel of the context stage at one request. -/
noncomputable def fixedAtomContextFuel
    (contracts : PublishedContracts) (requestedRate : ℕ)
    (table : NPOracleProgram) (tableFuel : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (bankShapeNumeralProgram (fixedRequiredDegree contracts requestedRate)))
      (linkPrograms contextSwapProgram (preserveRightProgram table)))
    2
    (linkFuel
      (linkPrograms contextSwapProgram (preserveRightProgram table))
      (preserveRightFuel
        (bankShapeNumeralFuel (fixedRequiredDegree contracts requestedRate)))
      (linkFuel (preserveRightProgram table) 4
        (preserveRightFuel (tableFuel request))))

/-- **`FixedAtomContextRuns` from the table stage alone.** -/
theorem fixedAtomContextRuns_ofTable
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target →
      target = fixedScheduleLength contracts clockDepth requestedRate target)
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ)
    (htable :
      FixedAtomTableRuns contracts clockDepth machine requestedRate pcp table
        tableBits tableFuel) :
    FixedAtomContextRuns contracts clockDepth machine requestedRate pcp
      (inverseAtomContextProgram (fixedRequiredDegree contracts requestedRate)
        table)
      (fixedAtomContextBits contracts clockDepth machine requestedRate pcp
        tableBits)
      (fixedAtomContextFuel contracts requestedRate table tableFuel) := by
  intro target hlarge input
  refine Eq.trans ?_
    (congrArg some
      (fixedAtomContext_ofRegisters contracts clockDepth machine requestedRate
        pcp hpresentation target (hdiagonal target hlarge)))
  exact run_occurrenceStage
    (run_contextDuplicateProgram target
      (fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩))
    (run_occurrenceStage
      (run_preserveRightProgram
        (bankShapeNumeralProgram (fixedRequiredDegree contracts requestedRate))
        target _ _
        (fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩)
        (fixedAdapterFrame contracts clockDepth requestedRate ⟨target, input⟩)
        _
        (run_bankShapeNumeralProgram
          (fixedRequiredDegree contracts requestedRate) target
          (bankSourceLength target)
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate)
            (sourceIndexOfLength target))
          (encodeBitInput input)))
      (run_occurrenceStage
        (run_contextSwapProgram target _
          (fixedAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩))
        (run_preserveRightProgram table target (tableBits ⟨target, input⟩)
          (tableFuel ⟨target, input⟩)
          (fixedAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)
          _ _ (htable target hlarge input))))

/-! ## 5. The two chain premises at the fixed bank, frame free

`BankFramedTargetChains.bankFramedChainProgram` and `run_bankFramedChainProgram`
read no schedule numeral — the point code is four right projections out of the
bank's frame at *every* public length — so only the width envelope is replayed
here. -/

/-- The width the wrapper is charged at one request on the fixed bank. -/
noncomputable def fixedBankFramedChainBits
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (chainBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (natBitLength
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (fixedBankRate contracts requestedRate)
        (LanguageEvaluationRequest.length request)
        (LanguageEvaluationRequest.code request)))
    (chainBits request)

/-- **The re-framing lemma at the published fixed bank.** -/
theorem run_bankFramedChainProgram_publishedFixed {chain : NPOracleProgram}
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    {target : ℕ} (input : BitInput target)
    {chainBits chainFuel fuel output : ℕ}
    (hchain :
      runNPOracleProgram chain chainBits chainFuel
        (initialNPOracleState target (encodeBitInput input)) = some output)
    (hfuel : linkFuel chain 5 chainFuel ≤ fuel) :
    runNPOracleProgram (bankFramedChainProgram chain)
        (fixedBankFramedChainBits contracts clockDepth requestedRate
          (fun _ => chainBits) ⟨target, input⟩)
        fuel
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate) target
            (encodeBitInput input))) =
      some output :=
  run_bankFramedChainProgram hchain hfuel

/-- **The Case-1 chain at the requested point code.** -/
def FixedCaseOnePointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (caseOne : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ target
    (hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target))
    (hrejects :
      ¬machine.toSemantic.accepts
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target))
    (haccepts :
      ∀ branchTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target),
        FixedCaseTwoAcceptance contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          branchTwo machine)
    (data : ScheduledCaseOneData
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target)
      (fixedRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target)),
    fixedTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target hyes = .caseOne data →
    ∀ input : BitInput target,
      runNPOracleProgram caseOne (chainBits ⟨target, input⟩)
          (chainFuel ⟨target, input⟩)
          (initialNPOracleState target (encodeBitInput input)) =
        some
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat

/-- **The Case-2 chain at the requested point code.** -/
def FixedCaseTwoPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ target
    (hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target)
    (hyes :
      (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
        (sourceLength
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target))
    (hrejects :
      ¬machine.toSemantic.accepts
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target))
    (haccepts :
      ∀ branchTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target),
        FixedCaseTwoAcceptance contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          branchTwo machine)
    (branchTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (fixedRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target)),
    fixedTargetBranch contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
        target hyes = .caseTwo branchTwo →
    ∀ input : BitInput target,
      runNPOracleProgram caseTwo (chainBits ⟨target, input⟩)
          (chainFuel ⟨target, input⟩)
          (initialNPOracleState target (encodeBitInput input)) =
        some
          (fixedCanonicalTargetFunction contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target hlarge hyes hrejects haccepts input).toNat

/-- **`hchainOne` from the point-code chain.** -/
theorem fixed_chainOne_ofPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (hone :
      FixedCaseOnePointRuns contracts clockDepth machine requestedRate caseOne
        chainBits chainFuel) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
          target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (haccepts :
        ∀ branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)
            branchTwo machine)
      (data : ScheduledCaseOneData
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedAmplifier contracts)
        (fixedRequiredDegree contracts requestedRate)
        (fixedSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
          target)
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target)),
      fixedTargetBranch contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target hyes = .caseOne data →
      ∀ input : BitInput target,
        runNPOracleProgram (bankFramedChainProgram caseOne)
            (fixedBankFramedChainBits contracts clockDepth requestedRate
              chainBits ⟨target, input⟩)
            (bankFramedChainFuel caseOne caseTwo chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (fixedBankRate contracts requestedRate) target
                (encodeBitInput input))) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts
              input).toNat := by
  intro target hlarge hyes hrejects haccepts data hbranch input
  exact run_bankFramedChainProgram_publishedFixed contracts clockDepth
    requestedRate input
    (hone target hlarge hyes hrejects haccepts data hbranch input)
    (Nat.le_max_left _ _)

/-- **`hchainTwo` from the point-code chain.** -/
theorem fixed_chainTwo_ofPointRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (caseOne caseTwo : NPOracleProgram)
    (chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (htwo :
      FixedCaseTwoPointRuns contracts clockDepth machine requestedRate caseTwo
        chainBits chainFuel) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
          target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (haccepts :
        ∀ branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)
            branchTwo machine)
      (branchTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (fixedRefuterInput contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target)),
      fixedTargetBranch contracts
          (publishedHierarchyOuterPCP contracts clockDepth) machine
          requestedRate target hyes = .caseTwo branchTwo →
      ∀ input : BitInput target,
        runNPOracleProgram (bankFramedChainProgram caseTwo)
            (fixedBankFramedChainBits contracts clockDepth requestedRate
              chainBits ⟨target, input⟩)
            (bankFramedChainFuel caseOne caseTwo chainFuel ⟨target, input⟩)
            (initialNPOracleState target
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (fixedBankRate contracts requestedRate) target
                (encodeBitInput input))) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts
              input).toNat := by
  intro target hlarge hyes hrejects haccepts branchTwo hbranch input
  exact run_bankFramedChainProgram_publishedFixed contracts clockDepth
    requestedRate input
    (htwo target hlarge hyes hrejects haccepts branchTwo hbranch input)
    (Nat.le_max_right _ _)

/-! ## 6. The atom-shape stage of the fixed diagonal cluster -/

/-- The context stage, then the count-and-pair stage. -/
noncomputable def fixedDiagonalShapeProgram
    (contracts : PublishedContracts) (requestedRate : ℕ)
    (table : NPOracleProgram) : NPOracleProgram :=
  inverseAtomShapeProgram
    (inverseAtomContextProgram (fixedRequiredDegree contracts requestedRate)
      table)

noncomputable def fixedDiagonalShapeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ) (compilerBits : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  fixedAtomShapeBits contracts clockDepth machine requestedRate pcp
    (fixedAtomContextBits contracts clockDepth machine requestedRate pcp
      tableBits)
    compilerBits

noncomputable def fixedDiagonalShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram) (tableFuel : LanguageEvaluationRequest → ℕ)
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  fixedAtomShapeFuel contracts clockDepth machine requestedRate pcp
    (fixedAtomContextFuel contracts requestedRate table tableFuel) compilerFuel

/-! ## 7. The frame-lowering adapter of the fixed diagonal cluster -/

noncomputable def fixedDiagonalAdapterProgram
    (contracts : PublishedContracts) (requestedRate : ℕ)
    (table : NPOracleProgram) : NPOracleProgram :=
  inverseFrameAdapterProgram
    (fixedDiagonalShapeProgram contracts requestedRate table)

noncomputable def fixedDiagonalAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ) (compilerBits : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  fixedFrameAdapterBits contracts clockDepth machine requestedRate pcp
    (fixedDiagonalShapeBits contracts clockDepth machine requestedRate pcp
      tableBits compilerBits)

noncomputable def fixedDiagonalAdapterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram) (tableFuel : LanguageEvaluationRequest → ℕ)
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseFrameAdapterFuel
    (fixedDiagonalShapeProgram contracts requestedRate table)
    (fixedDiagonalShapeFuel contracts clockDepth machine requestedRate pcp table
      tableFuel compilerFuel)

/-! ## 8. `bodyRun` from the fixed cluster's frame-free residuals -/

set_option maxHeartbeats 1600000 in
-- The dispatched body's envelopes are nested link terms over the whole stream.
/-- **The fixed schedule's `bodyRun`, from the diagonal cluster's residuals.**
`FixedScheduleAtomLoop.fixed_bodyRun_ofPresentation` with its adapter premise
and its two chain premises replaced by statements in which the numeral bank does
not appear. -/
theorem fixed_bodyRun_ofDiagonalCluster
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
        target →
      target = fixedScheduleLength contracts clockDepth requestedRate target)
    (table caseOne caseTwo : NPOracleProgram)
    (tableBits tableFuel chainBits chainFuel : LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (htable :
      FixedAtomTableRuns contracts clockDepth machine requestedRate pcp table
        tableBits tableFuel)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (fixedAtomCount contracts clockDepth machine requestedRate pcp target)
          (fixedAtomContext contracts clockDepth machine requestedRate pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (fixedAtomContext contracts clockDepth machine requestedRate pcp
                target)
              0
              (fixedAtomCount contracts clockDepth machine requestedRate pcp
                target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (fixedScheduleInput contracts clockDepth machine requestedRate
                target)
              (fixedScheduleBound contracts clockDepth requestedRate target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (fixedAtomContext contracts clockDepth machine requestedRate pcp
              target)
            0
            (fixedAtomCount contracts clockDepth machine requestedRate pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        fixedAtomCount contracts clockDepth machine requestedRate pcp target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target))
          (pcp.nativeWidth
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (pcp.queryCount
            (fixedScheduleLength contracts clockDepth requestedRate target))
          (fixedScheduleBound contracts clockDepth requestedRate target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      FixedCompilerRuns contracts clockDepth machine requestedRate pcp
        compilerBits compilerFuel)
    (hchainOne :
      FixedCaseOnePointRuns contracts clockDepth machine requestedRate caseOne
        chainBits chainFuel)
    (hchainTwo :
      FixedCaseTwoPointRuns contracts clockDepth machine requestedRate caseTwo
        chainBits chainFuel) :
    ∀ target
      (hlarge :
        fixedCaseOneTargetOnset contracts
          (publishedHierarchyOuterPCP contracts clockDepth) requestedRate ≤
          target)
      (hyes :
        (publishedRefuterSource contracts clockDepth).hierarchyMachine.accepts
          (sourceLength
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (hrejects :
        ¬machine.toSemantic.accepts
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target))
      (haccepts :
        ∀ branchTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (fixedRefuterInput contracts
            (publishedHierarchyOuterPCP contracts clockDepth) machine
            requestedRate target),
          FixedCaseTwoAcceptance contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target)
            branchTwo machine),
      ∀ input : BitInput target,
        runNPOracleProgram
            (bankDispatchedBodyProgram
              (emittedBranchSelectorProgram
                (fixedBankEmitterProgram
                  (fixedDiagonalAdapterProgram contracts requestedRate table)))
              (bankFramedChainProgram caseOne)
              (bankFramedChainProgram caseTwo))
            (fixedDispatchedBodyBits contracts clockDepth requestedRate
              (fixedBankSelectorBits contracts clockDepth machine requestedRate
                (fixedBankEmitterBits contracts clockDepth machine requestedRate
                  pcp
                  (fixedDiagonalAdapterBits contracts clockDepth machine
                    requestedRate pcp tableBits compilerBits)
                  rangeBits))
              (fixedBankFramedChainBits contracts clockDepth requestedRate
                chainBits) ⟨target, input⟩)
            (bankDispatchedBodyFuel (bankFramedChainProgram caseOne)
              (bankFramedChainProgram caseTwo)
              (fixedBankSelectorFuel contracts clockDepth machine requestedRate
                (fixedBankEmitterFuel contracts clockDepth machine requestedRate
                  pcp
                  (fixedDiagonalAdapterFuel contracts clockDepth machine
                    requestedRate pcp table tableFuel compilerFuel)
                  compilerFuel))
              (bankFramedChainFuel caseOne caseTwo chainFuel) ⟨target, input⟩)
            (initialNPOracleState target
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (fixedBankRate contracts requestedRate) target
                (encodeBitInput input))) =
          some
            (fixedCanonicalTargetFunction contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              requestedRate target hlarge hyes hrejects haccepts input).toNat :=
  fixed_bodyRun_ofPresentation contracts clockDepth machine requestedRate pcp
    hpresentation
    (fixedDiagonalAdapterProgram contracts requestedRate table)
    (bankFramedChainProgram caseOne) (bankFramedChainProgram caseTwo)
    (fixedDiagonalAdapterBits contracts clockDepth machine requestedRate pcp
      tableBits compilerBits)
    (fixedDiagonalAdapterFuel contracts clockDepth machine requestedRate pcp
      table tableFuel compilerFuel)
    (fixedBankFramedChainBits contracts clockDepth requestedRate chainBits)
    (bankFramedChainFuel caseOne caseTwo chainFuel)
    rangeBits compilerBits compilerFuel
    (fixedFrameAdapterRuns_ofShape contracts clockDepth machine requestedRate
      pcp (fixedDiagonalShapeProgram contracts requestedRate table)
      (fixedDiagonalShapeBits contracts clockDepth machine requestedRate pcp
        tableBits compilerBits)
      (fixedDiagonalShapeFuel contracts clockDepth machine requestedRate pcp
        table tableFuel compilerFuel)
      (fixedAtomShapeRuns_ofContext contracts clockDepth machine requestedRate
        pcp
        (inverseAtomContextProgram (fixedRequiredDegree contracts requestedRate)
          table)
        (fixedAtomContextBits contracts clockDepth machine requestedRate pcp
          tableBits)
        (fixedAtomContextFuel contracts requestedRate table tableFuel)
        compilerBits compilerFuel
        (fixedAtomContextRuns_ofTable contracts clockDepth machine requestedRate
          pcp hpresentation hdiagonal table tableBits tableFuel htable)
        hcompiler))
    hpositive hlengthBits hrangeBits hlistBits hcallBits hcalleeBits hcompiler
    (fixed_chainOne_ofPointRuns contracts clockDepth machine requestedRate
      caseOne caseTwo chainBits chainFuel hchainOne)
    (fixed_chainTwo_ofPointRuns contracts clockDepth machine requestedRate
      caseOne caseTwo chainBits chainFuel hchainTwo)

end NearCubicWires.FixedScheduleDiagonalClosure

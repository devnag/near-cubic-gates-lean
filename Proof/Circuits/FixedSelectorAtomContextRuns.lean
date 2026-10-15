import Proof.Circuits.SelectorDrivenAtomContext

/-!
# The fixed atom-context runs at the selector-driven frame

`BankAtomContextRegisters.fixedAtomContextRuns_ofTable` produces
`InverseAtomContextRuns` at the *log-decoded* bank frame
`inverseAdapterFrame … = publishedBankFrame … target`, threading `hdiagonal` to
identify that frame's registers with the chain's.  This module produces the
same context — the loop's public request context `fixedAtomContext … target`
— at the **selector-driven frame**
`selectorDrivenBankFrame … (fixedSelectedSource … target)`, with **no
`hdiagonal`**: the frame is the chain's frame by construction, and
`SelectorDrivenAtomContext.fixedAtomContext_ofSelectorRegisters` is the
`hdiagonal`-free register identification.

Only the register-width bits change (`fixedSelectorAtomContextBits`); the
program (`inverseAtomContextProgram`) and the fuel
(`fixedAtomContextFuel`) are frame-independent and reused verbatim.  This is
site 1 of the body-chain replay that deletes `hdiagonal` from the roots.
-/

namespace NearCubicWires.FixedSelectorAtomContextReplay

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.CanonicalBinary
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
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

open private contextDuplicateProgram contextDuplicateBits
  run_contextDuplicateProgram contextSwapProgram contextSwapBits
  run_contextSwapProgram from Proof.MachineModel.BankAtomContextRegisters

open private frameDuplicateProgram frameDuplicateBits run_frameDuplicateProgram
  from Proof.MachineModel.BankFrameLoweringAdapter

/-! ## 1. The selector-driven adapter frame -/

/-- The selector-driven bank's frame at one request: the chain's own frame,
built by the selector bank rather than decoded from the request length. -/
noncomputable def fixedSelectorAdapterFrame
    (contracts : PublishedContracts) (clockDepth : ℕ) (requestedRate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorDrivenBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (fixedBankRate contracts requestedRate)
    (fixedSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request)

/-! ## 2. The table and context runs at the selector frame -/

/-- **The adapter's last residual, at the selector frame.**  From the selector
bank's frame the table stage returns the balanced encoding of the projection
runner's call outputs.  Frame-shifted twin of `InverseAtomTableRuns`. -/
def FixedSelectorAtomTableRuns
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
        (publishedHierarchyOuterPCP contracts clockDepth)
        requestedRate ≤ target)
    (input : BitInput target),
    runNPOracleProgram table (tableBits ⟨target, input⟩)
        (tableFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (fixedScheduleInput contracts clockDepth machine requestedRate
              target)))

/-- **The context half at the selector frame.**  Frame-shifted twin of
`InverseAtomContextRuns`; same output `fixedAtomContext … target`. -/
def FixedSelectorAtomContextRuns
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
        (publishedHierarchyOuterPCP contracts clockDepth)
        requestedRate ≤ target)
    (input : BitInput target),
    runNPOracleProgram context (contextBits ⟨target, input⟩)
        (contextFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (fixedAtomContext contracts clockDepth machine requestedRate pcp
          target)

/-- Width of the context stage at the selector frame: the frozen
`fixedAtomContextBits` mirror with the chain's registers. -/
noncomputable def fixedSelectorAtomContextBits
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
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        request))
    (occurrenceStageBits (LanguageEvaluationRequest.length request)
      (preserveRightBits
        (bankShapeNumeralBits
          (fixedRequiredDegree contracts requestedRate)
          (LanguageEvaluationRequest.length request)
          (fixedScheduleLength contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request))
          (fixedSelectorBankWidth contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request))
          (fixedSelectorBankQueryCount contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request))
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate)
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              (LanguageEvaluationRequest.length request)))
          (LanguageEvaluationRequest.code request))
        (fixedSelectorAdapterFrame contracts clockDepth requestedRate
          request)
        (fixedSelectorAdapterFrame contracts clockDepth requestedRate
          request)
        (bankShapeNumerals
          (oracleSizeBound
            (fixedRequiredDegree contracts requestedRate)
            (fixedSelectorBankWidth contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request)))
          (fixedSelectorBankWidth contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request))
          (fixedSelectorBankQueryCount contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request))))
      (occurrenceStageBits (LanguageEvaluationRequest.length request)
        (contextSwapBits
          (bankShapeNumerals
            (oracleSizeBound
              (fixedRequiredDegree contracts requestedRate)
              (fixedSelectorBankWidth contracts clockDepth requestedRate
                (LanguageEvaluationRequest.length request)))
            (fixedSelectorBankWidth contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request))
            (fixedSelectorBankQueryCount contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request)))
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            request))
        (preserveRightBits (tableBits request)
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            request)
          (bankShapeNumerals
            (oracleSizeBound
              (fixedRequiredDegree contracts requestedRate)
              (fixedSelectorBankWidth contracts clockDepth requestedRate
                (LanguageEvaluationRequest.length request)))
            (fixedSelectorBankWidth contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request))
            (fixedSelectorBankQueryCount contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request)))
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (fixedScheduleInput contracts clockDepth machine
                requestedRate
                (LanguageEvaluationRequest.length request)))))))

/-- **`FixedSelectorAtomContextRuns` from the selector table stage.**  The
register half is executed from the selector bank's frame; the identification is
`fixedAtomContext_ofSelectorRegisters` — no `hdiagonal`, only the
presentation premise. -/
theorem fixedSelectorAtomContextRuns_ofTable
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PaddedProjectionPresentation.PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ)
    (htable :
      FixedSelectorAtomTableRuns contracts clockDepth machine requestedRate
        pcp table tableBits tableFuel) :
    FixedSelectorAtomContextRuns contracts clockDepth machine requestedRate
      pcp
      (inverseAtomContextProgram
        (fixedRequiredDegree contracts requestedRate)
        table)
      (fixedSelectorAtomContextBits contracts clockDepth machine
        requestedRate pcp tableBits)
      (fixedAtomContextFuel contracts requestedRate table tableFuel) := by
  intro target hlarge input
  refine Eq.trans ?_
    (congrArg some
      (fixedAtomContext_ofSelectorRegisters contracts clockDepth machine
        requestedRate pcp hpresentation target))
  exact run_occurrenceStage
    (run_contextDuplicateProgram target
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        ⟨target, input⟩))
    (run_occurrenceStage
      (run_preserveRightProgram
        (bankShapeNumeralProgram
          (fixedRequiredDegree contracts requestedRate))
        target _ _
        (fixedSelectorAdapterFrame contracts clockDepth requestedRate
          ⟨target, input⟩)
        (fixedSelectorAdapterFrame contracts clockDepth requestedRate
          ⟨target, input⟩)
        _
        (run_bankShapeNumeralProgram
          (fixedRequiredDegree contracts requestedRate)
          target
          (fixedScheduleLength contracts clockDepth requestedRate target)
          (fixedSelectorBankWidth contracts clockDepth requestedRate
            target)
          (fixedSelectorBankQueryCount contracts clockDepth requestedRate
            target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (fixedBankRate contracts requestedRate)
            (fixedSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
              target))
          (encodeBitInput input)))
      (run_occurrenceStage
        (run_contextSwapProgram target _
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩))
        (run_preserveRightProgram table target (tableBits ⟨target, input⟩)
          (tableFuel ⟨target, input⟩)
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)
          _ _ (htable target hlarge input))))

/-! ## 3. The atom-shape runs at the selector frame -/

/-- **The atom-shape stage at the selector frame.**  Frame-shifted twin of
`InverseAtomShapeRuns`; same output `fixedAdapterRange`. -/
def FixedSelectorAtomShapeRuns
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
        (publishedHierarchyOuterPCP contracts clockDepth)
        requestedRate ≤ target)
    (input : BitInput target),
    runNPOracleProgram shape (shapeBits ⟨target, input⟩)
        (shapeFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (fixedAdapterRange contracts clockDepth machine requestedRate pcp
          ⟨target, input⟩)

/-- **`FixedSelectorAtomShapeRuns` from the selector context.**  The
count-and-pair tail is frame-independent; only the context stage sees the
selector frame. -/
theorem fixedSelectorAtomShapeRuns_ofContext
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
      FixedSelectorAtomContextRuns contracts clockDepth machine
        requestedRate pcp context contextBits contextFuel)
    (hcompiler :
      FixedCompilerRuns contracts clockDepth machine requestedRate pcp
        compilerBits compilerFuel) :
    FixedSelectorAtomShapeRuns contracts clockDepth machine requestedRate
      pcp (inverseAtomShapeProgram context)
      (fixedAtomShapeBits contracts clockDepth machine requestedRate pcp
        contextBits compilerBits)
      (fixedAtomShapeFuel contracts clockDepth machine requestedRate pcp
        contextFuel compilerFuel) := by
  intro target hlarge input
  exact run_occurrenceStage (hcontext target hlarge input)
    (run_atomShapeCountProgram target
      (fixedAtomContext contracts clockDepth machine requestedRate pcp
        target)
      _ _
      (fixedAtomCount contracts clockDepth machine requestedRate pcp
        target)
      (run_structuralAtomCountProgram_index pcp
        (fixedScheduleInput contracts clockDepth machine requestedRate
          target)
        target (fixedScheduleBound contracts clockDepth requestedRate
          target)
        (compilerBits target 0) (compilerFuel target 0)
        (hcompiler target 0
          (fixedAtomCount_pos contracts clockDepth machine requestedRate
            pcp target))))

/-! ## 4. The frame-adapter runs at the selector frame -/

/-- **The frame-lowering premise at the selector frame.**  Frame-shifted twin
of `InverseFrameAdapterRuns` — the retained frame is the selector frame. -/
def FixedSelectorFrameAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      fixedCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        requestedRate ≤ target)
    (input : BitInput target),
    runNPOracleProgram adapter (adapterBits ⟨target, input⟩)
        (adapterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩)) =
      some
        (Nat.pair
          (generatedBalancedRangeInput
            (fixedAtomCount contracts clockDepth machine requestedRate pcp
              target)
            (fixedAtomContext contracts clockDepth machine requestedRate
              pcp target))
          (fixedSelectorAdapterFrame contracts clockDepth requestedRate
            ⟨target, input⟩))

/-- Width of the frame adapter at the selector frame. -/
noncomputable def fixedSelectorFrameAdapterBits
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
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        request))
    (preserveRightBits (shapeBits request)
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        request)
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        request)
      (fixedAdapterRange contracts clockDepth machine requestedRate pcp
        request))

/-- **`FixedSelectorFrameAdapterRuns` from the selector shape.**  The frame
duplication and retention are frame-independent transducers; the retained frame
is the selector frame. -/
theorem fixedSelectorFrameAdapterRuns_ofShape
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ)
    (hshape :
      FixedSelectorAtomShapeRuns contracts clockDepth machine requestedRate
        pcp shape shapeBits shapeFuel) :
    FixedSelectorFrameAdapterRuns contracts clockDepth machine requestedRate
      pcp (inverseFrameAdapterProgram shape)
      (fixedSelectorFrameAdapterBits contracts clockDepth machine
        requestedRate pcp shapeBits)
      (inverseFrameAdapterFuel shape shapeFuel) := by
  intro target hlarge input
  exact run_occurrenceStage
    (run_frameDuplicateProgram target
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        ⟨target, input⟩))
    (run_preserveRightProgram shape target (shapeBits ⟨target, input⟩)
      (shapeFuel ⟨target, input⟩)
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        ⟨target, input⟩)
      (fixedSelectorAdapterFrame contracts clockDepth requestedRate
        ⟨target, input⟩)
      (fixedAdapterRange contracts clockDepth machine requestedRate pcp
        ⟨target, input⟩)
      (hshape target hlarge input))

end NearCubicWires.FixedSelectorAtomContextReplay

import Proof.Circuits.SelectorDrivenAtomContext

/-!
# The atom-context runs at the selector-driven frame

`BankAtomContextRegisters.inverseAtomContextRuns_ofTable` produces
`InverseAtomContextRuns` at the *log-decoded* bank frame
`inverseAdapterFrame … = publishedBankFrame … target`, threading `hdiagonal` to
identify that frame's registers with the chain's.  This module produces the
same context — the loop's public request context `inverseAtomContext … target`
— at the **selector-driven frame**
`selectorDrivenBankFrame … (inverseChainSourceIndex … target)`, with **no
`hdiagonal`**: the frame is the chain's frame by construction, and
`SelectorDrivenAtomContext.inverseAtomContext_ofSelectorRegisters` is the
`hdiagonal`-free register identification.

Only the register-width bits change (`inverseSelectorAtomContextBits`); the
program (`inverseAtomContextProgram`) and the fuel
(`inverseAtomContextFuel`) are frame-independent and reused verbatim.  This is
site 1 of the body-chain replay that deletes `hdiagonal` from the roots.
-/

namespace NearCubicWires.SelectorDrivenAtomContextRuns

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
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
noncomputable def inverseSelectorAdapterFrame
    (contracts : PublishedContracts) (clockDepth : ℕ) (advantageExponent : ℝ)
    (request : LanguageEvaluationRequest) : ℕ :=
  selectorDrivenBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseChainSourceIndex contracts clockDepth advantageExponent
      (LanguageEvaluationRequest.length request))
    (LanguageEvaluationRequest.code request)

/-! ## 2. The table and context runs at the selector frame -/

/-- **The adapter's last residual, at the selector frame.**  From the selector
bank's frame the table stage returns the balanced encoding of the projection
runner's call outputs.  Frame-shifted twin of `InverseAtomTableRuns`. -/
def InverseSelectorAtomTableRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram table (tableBits ⟨target, input⟩)
        (tableFuel ⟨target, input⟩)
        (initialNPOracleState target
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)))

/-- **The context half at the selector frame.**  Frame-shifted twin of
`InverseAtomContextRuns`; same output `inverseAtomContext … target`. -/
def InverseSelectorAtomContextRuns
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
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)

/-- Width of the context stage at the selector frame: the frozen
`inverseAtomContextBits` mirror with the chain's registers. -/
noncomputable def inverseSelectorAtomContextBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (tableBits : LanguageEvaluationRequest → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (contextDuplicateBits
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request))
    (occurrenceStageBits (LanguageEvaluationRequest.length request)
      (preserveRightBits
        (bankShapeNumeralBits
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (LanguageEvaluationRequest.length request)
          (inverseScheduleLength contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request))
          (inverseSelectorBankWidth contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request))
          (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request))
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request)))
          (LanguageEvaluationRequest.code request))
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          request)
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          request)
        (bankShapeNumerals
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request)))
          (inverseSelectorBankWidth contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request))
          (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
            (LanguageEvaluationRequest.length request))))
      (occurrenceStageBits (LanguageEvaluationRequest.length request)
        (contextSwapBits
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSelectorBankWidth contracts clockDepth advantageExponent
                (LanguageEvaluationRequest.length request)))
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request))
            (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request)))
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request))
        (preserveRightBits (tableBits request)
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseSelectorBankWidth contracts clockDepth advantageExponent
                (LanguageEvaluationRequest.length request)))
            (inverseSelectorBankWidth contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request))
            (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
              (LanguageEvaluationRequest.length request)))
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent
                (LanguageEvaluationRequest.length request)))))))

/-- **`InverseSelectorAtomContextRuns` from the selector table stage.**  The
register half is executed from the selector bank's frame; the identification is
`inverseAtomContext_ofSelectorRegisters` — no `hdiagonal`, only the
presentation premise. -/
theorem inverseSelectorAtomContextRuns_ofTable
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
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
      InverseSelectorAtomTableRuns contracts clockDepth machine advantageExponent
        pcp table tableBits tableFuel) :
    InverseSelectorAtomContextRuns contracts clockDepth machine advantageExponent
      pcp
      (inverseAtomContextProgram
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        table)
      (inverseSelectorAtomContextBits contracts clockDepth machine
        advantageExponent pcp tableBits)
      (inverseAtomContextFuel contracts advantageExponent table tableFuel) := by
  intro target hlarge input
  refine Eq.trans ?_
    (congrArg some
      (inverseAtomContext_ofSelectorRegisters contracts clockDepth machine
        advantageExponent pcp hpresentation target))
  exact run_occurrenceStage
    (run_contextDuplicateProgram target
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩))
    (run_occurrenceStage
      (run_preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        target _ _
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          ⟨target, input⟩)
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          ⟨target, input⟩)
        _
        (run_bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          target
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          (inverseSelectorBankWidth contracts clockDepth advantageExponent
            target)
          (inverseSelectorBankQueryCount contracts clockDepth advantageExponent
            target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseChainSourceIndex contracts clockDepth advantageExponent
              target))
          (encodeBitInput input)))
      (run_occurrenceStage
        (run_contextSwapProgram target _
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩))
        (run_preserveRightProgram table target (tableBits ⟨target, input⟩)
          (tableFuel ⟨target, input⟩)
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)
          _ _ (htable target hlarge input))))

/-! ## 3. The atom-shape runs at the selector frame -/

/-- **The atom-shape stage at the selector frame.**  Frame-shifted twin of
`InverseAtomShapeRuns`; same output `inverseAdapterRange`. -/
def InverseSelectorAtomShapeRuns
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
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
          ⟨target, input⟩)

/-- **`InverseSelectorAtomShapeRuns` from the selector context.**  The
count-and-pair tail is frame-independent; only the context stage sees the
selector frame. -/
theorem inverseSelectorAtomShapeRuns_ofContext
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
      InverseSelectorAtomContextRuns contracts clockDepth machine
        advantageExponent pcp context contextBits contextFuel)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseSelectorAtomShapeRuns contracts clockDepth machine advantageExponent
      pcp (inverseAtomShapeProgram context)
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

/-! ## 4. The frame-adapter runs at the selector frame -/

/-- **The frame-lowering premise at the selector frame.**  Frame-shifted twin
of `InverseFrameAdapterRuns` — the retained frame is the selector frame. -/
def InverseSelectorFrameAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ (target : ℕ)
    (_hlarge :
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target)
    (input : BitInput target),
    runNPOracleProgram adapter (adapterBits ⟨target, input⟩)
        (adapterFuel ⟨target, input⟩)
        (initialNPOracleState target
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩)) =
      some
        (Nat.pair
          (generatedBalancedRangeInput
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target))
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            ⟨target, input⟩))

/-- Width of the frame adapter at the selector frame. -/
noncomputable def inverseSelectorFrameAdapterBits
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
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request))
    (preserveRightBits (shapeBits request)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
        request))

/-- **`InverseSelectorFrameAdapterRuns` from the selector shape.**  The frame
duplication and retention are frame-independent transducers; the retained frame
is the selector frame. -/
theorem inverseSelectorFrameAdapterRuns_ofShape
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (shape : NPOracleProgram)
    (shapeBits shapeFuel : LanguageEvaluationRequest → ℕ)
    (hshape :
      InverseSelectorAtomShapeRuns contracts clockDepth machine advantageExponent
        pcp shape shapeBits shapeFuel) :
    InverseSelectorFrameAdapterRuns contracts clockDepth machine advantageExponent
      pcp (inverseFrameAdapterProgram shape)
      (inverseSelectorFrameAdapterBits contracts clockDepth machine
        advantageExponent pcp shapeBits)
      (inverseFrameAdapterFuel shape shapeFuel) := by
  intro target hlarge input
  exact run_occurrenceStage
    (run_frameDuplicateProgram target
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩))
    (run_preserveRightProgram shape target (shapeBits ⟨target, input⟩)
      (shapeFuel ⟨target, input⟩)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩)
      (inverseAdapterRange contracts clockDepth machine advantageExponent pcp
        ⟨target, input⟩)
      (hshape target hlarge input))

end NearCubicWires.SelectorDrivenAtomContextRuns

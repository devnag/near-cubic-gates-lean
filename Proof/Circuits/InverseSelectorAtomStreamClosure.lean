import Proof.Circuits.InverseDescriptionAtomStream
import Proof.Circuits.InverseSelectorDirectBodyClosure

/-!
# The inverse description atom stream at the selector-driven bank

The selector bank first computes the scheduled source length and loads the
exact chain frame.  The existing selector-frame adapter and balanced atom range
then produce the description atom stream.  The frame-local numeral projection
supplies native width and the small-oracle bound, so no schedule diagonal is
needed.
-/

namespace NearCubicWires.InverseSelectorAtomStreamClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.InverseDescriptionAtomStream
open NearCubicWires.InverseLengthStage
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyClosure
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private contextSwapProgram contextSwapBits run_contextSwapProgram from
  Proof.MachineModel.BankAtomContextRegisters

private theorem inverseSelectorAdapterFrame_fixedTarget
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩ =
      selectorDrivenBankFrame
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
          advantageExponent target)
        target := by
  unfold inverseSelectorAdapterFrame
    LanguageEvaluationRequest.length LanguageEvaluationRequest.code
    SelectorDrivenAtomContext.inverseChainSourceIndex
    BankRegisterCaseOneChain.inverseChainSourceIndex
  rw [encode_fixedTargetCodeInput]

noncomputable def inverseSelectorAtomStreamProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  linkPrograms
    (publishedSourceDrivenBankProgram
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthProgram contracts clockDepth advantageExponent))
    (linkPrograms
      (inverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (inverseAtomStreamLoopProgram contracts advantageExponent))

noncomputable def inverseSelectorAtomStreamTailBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  let sourceIndex :=
    inverseChainSourceIndex contracts clockDepth advantageExponent target
  let sourceLen := sourceLength sourceIndex
  let width :=
    scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth) sourceIndex
  let queryCount :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount sourceLen
  let copies := inverseCopies
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) sourceIndex
  let atoms :=
    inverseFrameAtoms contracts clockDepth machine advantageExponent target
  let frame := selectorDrivenBankFrame
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) sourceIndex target
  occurrenceStageBits target (contextSwapBits atoms frame) <|
    occurrenceStageBits target
      (preserveRightBits
        (bankShapeNumeralBits
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          target sourceLen width queryCount copies target)
        frame atoms
        (bankShapeNumerals
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)) width)
          width queryCount))
      (descriptionAtomTailBits atoms width queryCount
        (oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)) width))

noncomputable def inverseSelectorAtomStreamLoopBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (rangeBits : ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (preserveRightBits (rangeBits target)
      (generatedBalancedRangeInput
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target))
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseFrameAtoms contracts clockDepth machine advantageExponent target))
    (inverseSelectorAtomStreamTailBits contracts clockDepth machine
      advantageExponent target)

noncomputable def inverseSelectorAtomStreamBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (rangeBits : ℕ → ℕ) (compilerBits : ℕ → ℕ → ℕ)
    (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (publishedSourceDrivenBankBits
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target
      (inverseLengthBits contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseScheduleLength contracts clockDepth advantageExponent target)
      target)
    (occurrenceStageBits target
      (inverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseSelectorAtomStreamLoopBits contracts clockDepth machine
        advantageExponent pcp rangeBits target))

noncomputable def inverseSelectorAtomStreamFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (inverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (inverseAtomStreamLoopProgram contracts advantageExponent))
    (publishedSourceDrivenBankFuel
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthFuel contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (linkFuel (inverseAtomStreamLoopProgram contracts advantageExponent)
      (inverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseAtomStreamLoopFuel contracts clockDepth machine advantageExponent
        pcp compilerFuel target))

set_option maxHeartbeats 1600000 in
-- The proof composes the selector bank, dependent atom range, and numeral tail.
theorem inverseDescriptionAtomStreamRuns_ofSelectorCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (inverseAtomContext contracts clockDepth machine advantageExponent
                pcp target)
              0
              (inverseAtomCount contracts clockDepth machine advantageExponent
                pcp target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)
              (inverseScheduleBound contracts clockDepth advantageExponent
                target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseDescriptionAtomStreamRuns contracts clockDepth machine
      advantageExponent
      (inverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp)
      (inverseSelectorAtomStreamBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits)
      (inverseSelectorAtomStreamFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) := by
  intro target hlarge
  let sourceIndex :=
    inverseChainSourceIndex contracts clockDepth advantageExponent target
  let sourceLen := sourceLength sourceIndex
  let width :=
    scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth) sourceIndex
  let queryCount :=
    (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount sourceLen
  let copies := inverseCopies
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) sourceIndex
  let atoms :=
    inverseFrameAtoms contracts clockDepth machine advantageExponent target
  let frame := selectorDrivenBankFrame
    (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent) sourceIndex target
  have hsourceLen :
      inverseScheduleLength contracts clockDepth advantageExponent target =
        sourceLen := by
    rfl
  have hframeEq :
      inverseSelectorAdapterFrame contracts clockDepth advantageExponent
          ⟨target, fixedTargetCodeInput target⟩ =
        frame := by
    exact inverseSelectorAdapterFrame_fixedTarget contracts clockDepth
      advantageExponent target
  have hbank₀ := run_inverseSelectorBank_closed contracts clockDepth
    advantageExponent target (fixedTargetCodeInput target)
  have hbank := hbank₀
  rw [encode_fixedTargetCodeInput, hsourceLen] at hbank
  change runNPOracleProgram
      (publishedSourceDrivenBankProgram
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (inverseLengthProgram contracts clockDepth advantageExponent))
      (publishedSourceDrivenBankBits
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target
        (inverseLengthBits contracts clockDepth advantageExponent
          ⟨target, fixedTargetCodeInput target⟩)
        sourceLen target)
      (publishedSourceDrivenBankFuel
        (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent)
        (inverseLengthFuel contracts clockDepth advantageExponent
          ⟨target, fixedTargetCodeInput target⟩)
        sourceLen)
      (initialNPOracleState target target) = some frame at hbank
  have hadapterRuns := inverseSelectorBodyAdapterRuns contracts clockDepth
    machine advantageExponent pcp hpresentation compilerBits compilerFuel
    hcompiler
  have hadapter := hadapterRuns target hlarge (fixedTargetCodeInput target)
  rw [hframeEq] at hadapter
  have hatoms := inverseScheduleAtoms_of_presentation contracts clockDepth
    machine advantageExponent pcp hpresentation target
  have hrange := run_structuralAtomRangeProgram_ofCompiler pcp
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)
    target (inverseScheduleBound contracts clockDepth advantageExponent target)
    (compilerBits target) (compilerFuel target) (hpositive target)
    (hlengthBits target) (hrangeBits target) (hlistBits target)
    (hcallBits target) (hcalleeBits target) (hcompiler target)
  rw [hatoms] at hrange
  have hshape := run_bankShapeNumeralProgram
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    target sourceLen width queryCount copies target
  have htail :
      runNPOracleProgram
          (inverseAtomStreamTailProgram contracts advantageExponent)
          (inverseSelectorAtomStreamTailBits contracts clockDepth machine
            advantageExponent target)
          (inverseAtomStreamTailFuel contracts advantageExponent)
          (initialNPOracleState target (Nat.pair atoms frame)) =
        some (Nat.pair atoms
          (Nat.pair width
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent)) width))) := by
    unfold inverseAtomStreamTailProgram inverseSelectorAtomStreamTailBits
      inverseAtomStreamTailFuel
    exact run_occurrenceStage (run_contextSwapProgram target atoms frame)
      (run_occurrenceStage
        (run_preserveRightProgram
          (bankShapeNumeralProgram
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)))
          target _ _ frame atoms _ hshape)
        (run_descriptionAtomTailProgram target atoms width queryCount
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent)) width)))
  have hloop := run_occurrenceStage
    (run_preserveRightProgram
      (structuralAtomRangeProgram structuralAtomCalleeProgram)
      target (rangeBits target)
      (structuralAtomRangeFuel structuralAtomCalleeProgram target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)
        (structuralAtomCalleeRequestFuel
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          (compilerFuel target)))
      (generatedBalancedRangeInput
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target))
      frame atoms hrange)
    htail
  have hbody := run_occurrenceStage hadapter hloop
  have hrun := run_occurrenceStage hbank hbody
  have hwidth :
      width =
        inverseFrameWidth contracts clockDepth advantageExponent target := by
    rfl
  have houtput :
      Nat.pair atoms
          (Nat.pair width
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent)) width)) =
        descriptionFrameSource
          (inverseFrameAtoms contracts clockDepth machine advantageExponent
            target)
          (inverseFrameWidth contracts clockDepth advantageExponent target)
          (inverseFrameBound contracts clockDepth advantageExponent target) := by
    rw [hwidth]
    rfl
  rw [houtput] at hrun
  simpa only [inverseSelectorAtomStreamProgram,
    inverseSelectorAtomStreamBits, inverseSelectorAtomStreamFuel,
    inverseSelectorAtomStreamLoopBits, inverseSelectorAtomStreamTailBits,
    inverseAtomStreamLoopProgram, inverseAtomStreamLoopFuel,
    hsourceLen, hframeEq, sourceIndex, sourceLen, width, queryCount, copies,
    atoms, frame] using hrun

/-! ## The selector body with its description stream installed -/

noncomputable def inverseSelectorCompiledBody
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  InverseSelectorDirectBodyClosure.inverseSelectorDirectBody contracts
    clockDepth machine advantageExponent pcp
    (inverseSelectorClosedEncodingProgram contracts clockDepth machine
      advantageExponent
      (inverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp))

noncomputable def inverseSelectorCompiledBodyBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (rangeBits : ℕ → ℕ) (compilerBits : ℕ → ℕ → ℕ) :
    LanguageEvaluationRequest → ℕ :=
  InverseSelectorDirectBodyClosure.inverseSelectorDirectBodyBits contracts
    clockDepth machine advantageExponent pcp rangeBits compilerBits
    (inverseSelectorClosedEncodingBits contracts clockDepth machine
      advantageExponent
      (inverseSelectorAtomStreamBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits))

noncomputable def inverseSelectorCompiledBodyFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  InverseSelectorDirectBodyClosure.inverseSelectorDirectBodyFuel contracts
    clockDepth machine advantageExponent pcp compilerFuel
    (inverseSelectorClosedEncodingProgram contracts clockDepth machine
      advantageExponent
      (inverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp))
    (inverseSelectorClosedEncodingFuel contracts clockDepth machine
      advantageExponent
      (inverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp)
      (inverseSelectorAtomStreamFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel))

set_option maxHeartbeats 1600000 in
-- This composition expands the exact range, compiler, stream, and branch ABIs.
theorem inverseSelectorDirectBodyRun_ofSelectorCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hpositive : ∀ target, 1 ≤ rangeBits target)
    (hlengthBits : ∀ target, natBitLength target ≤ rangeBits target)
    (hrangeBits : ∀ target,
      generatedBalancedRangeRequiredBits target
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target) ≤
        rangeBits target)
    (hlistBits : ∀ target,
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (inverseAtomContext contracts clockDepth machine advantageExponent
                pcp target)
              0
              (inverseAtomCount contracts clockDepth machine advantageExponent
                pcp target))) ≤
        rangeBits target)
    (hcallBits : ∀ target,
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target)
              (inverseScheduleBound contracts clockDepth advantageExponent
                target)
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)) ≤
        rangeBits target)
    (hcalleeBits : ∀ target index,
      index <
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target →
      structuralAtomCalleeBits target
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          index (compilerBits target index) ≤
        rangeBits target)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseSelectorDirectBodyClosure.InverseSelectorDirectBodyRun contracts
      clockDepth machine advantageExponent
      (inverseSelectorCompiledBody contracts clockDepth machine
        advantageExponent pcp)
      (inverseSelectorCompiledBodyBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits)
      (inverseSelectorCompiledBodyFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) := by
  have hstream := inverseDescriptionAtomStreamRuns_ofSelectorCompiler contracts
    clockDepth machine advantageExponent pcp hpresentation rangeBits
    compilerBits compilerFuel hpositive hlengthBits hrangeBits hlistBits
    hcallBits hcalleeBits hcompiler
  exact InverseSelectorDirectBodyClosure.inverseSelectorDirectBodyRun_ofAtomStream
    contracts clockDepth machine advantageExponent pcp hpresentation rangeBits
    compilerBits compilerFuel hpositive hlengthBits hrangeBits hlistBits
    hcallBits hcalleeBits hcompiler
    (inverseSelectorAtomStreamProgram contracts clockDepth machine
      advantageExponent pcp)
    (inverseSelectorAtomStreamBits contracts clockDepth machine
      advantageExponent pcp rangeBits compilerBits)
    (inverseSelectorAtomStreamFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    hstream

end NearCubicWires.InverseSelectorAtomStreamClosure

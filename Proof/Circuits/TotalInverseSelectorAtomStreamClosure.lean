import Proof.Circuits.InverseSelectorAtomStreamClosure
import Proof.MachineModel.TotalInverseSelectorAtomStreamSourceBank
import Proof.Circuits.TotalSelectorBodyAdapter
import Proof.MachineModel.TotalStructuralAtomRangeProgram

/-!
# The guarded inverse selector atom stream

The source-driven selector bank and description numeral tail are frozen.  This
module replaces only the selector-frame adapter and balanced atom-range callee,
then exports the existing `InverseDescriptionAtomStreamRuns` interface.
-/

namespace NearCubicWires.TotalInverseSelectorAtomStreamClosure

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
open NearCubicWires.InverseSelectorAtomStreamClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.SelectorDrivenBodyClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseSelectorAtomStreamSourceBank
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalStructuralAtomCalleeProgram
open NearCubicWires.TotalStructuralAtomRangeProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter

open private contextSwapBits contextSwapProgram run_contextSwapProgram from
  Proof.MachineModel.BankAtomContextRegisters
open private inverseSelectorAdapterFrame_fixedTarget from
  Proof.Circuits.InverseSelectorAtomStreamClosure

/-! ## 1. The guarded stream and resources -/

noncomputable def totalInverseAtomStreamLoopProgram
    (contracts : PublishedContracts) (advantageExponent : ℝ) :
    NPOracleProgram :=
  linkPrograms
    (preserveRightProgram
      (structuralAtomRangeProgram totalStructuralAtomCalleeProgram))
    (inverseAtomStreamTailProgram contracts advantageExponent)

noncomputable def totalInverseAtomStreamLoopFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel (inverseAtomStreamTailProgram contracts advantageExponent)
    (preserveRightFuel
      (structuralAtomRangeFuel totalStructuralAtomCalleeProgram target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)
        (totalStructuralAtomCalleeRequestFuel
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
          (compilerFuel target))))
    (inverseAtomStreamTailFuel contracts advantageExponent)

noncomputable def totalInverseSelectorAtomStreamProgram
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
      (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseAtomStreamLoopProgram contracts advantageExponent))

noncomputable def totalInverseSelectorAtomStreamBits
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
      (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseSelectorAtomStreamLoopBits contracts clockDepth machine
        advantageExponent pcp rangeBits target))

noncomputable def totalInverseSelectorAtomStreamFuel
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
      (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseAtomStreamLoopProgram contracts advantageExponent))
    (publishedSourceDrivenBankFuel
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthFuel contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (linkFuel (totalInverseAtomStreamLoopProgram contracts advantageExponent)
      (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel
        ⟨target, fixedTargetCodeInput target⟩)
      (totalInverseAtomStreamLoopFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel target))

/-! ## 2. The guarded atom-stream consumer -/

set_option maxHeartbeats 1600000 in
-- The proof composes the selector bank, guarded adapter/range, and numeral tail.
theorem totalInverseDescriptionAtomStreamRuns_ofSelectorCompiler
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
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel) :
    InverseDescriptionAtomStreamRuns contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorAtomStreamBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits)
      (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
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
  have hbank := run_totalInverseSelectorSourceBank_fixedTarget contracts
    clockDepth advantageExponent target
  rw [hsourceLen]
    at hbank
  have hadapterRuns := totalInverseSelectorBodyAdapterRuns contracts clockDepth
    machine advantageExponent pcp hpresentation compilerBits compilerFuel
    hcompiler
  have hadapter := hadapterRuns target hlarge (fixedTargetCodeInput target)
  rw [hframeEq] at hadapter
  have hatoms := inverseScheduleAtoms_of_presentation contracts clockDepth
    machine advantageExponent pcp hpresentation target
  have hrange := run_totalStructuralAtomRangeProgram_ofCompiler pcp
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
        some
          (Nat.pair atoms
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
      (structuralAtomRangeProgram totalStructuralAtomCalleeProgram)
      target (rangeBits target)
      (structuralAtomRangeFuel totalStructuralAtomCalleeProgram target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)
        (totalStructuralAtomCalleeRequestFuel
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
  simpa only [totalInverseSelectorAtomStreamProgram,
    totalInverseSelectorAtomStreamBits, totalInverseSelectorAtomStreamFuel,
    inverseSelectorAtomStreamLoopBits, inverseSelectorAtomStreamTailBits,
    totalInverseAtomStreamLoopProgram, totalInverseAtomStreamLoopFuel,
    hsourceLen, hframeEq, sourceIndex, sourceLen, width, queryCount, copies,
    atoms, frame] using hrun

end NearCubicWires.TotalInverseSelectorAtomStreamClosure

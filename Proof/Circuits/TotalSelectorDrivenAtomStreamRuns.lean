import Proof.Circuits.TotalSelectorDrivenAtomStreamContract
import Proof.Circuits.TotalSelectorDrivenBodyAdapterRuns

/-! # Concrete all-request guarded description atom stream -/

namespace NearCubicWires.TotalSelectorDrivenAtomStreamRuns

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
open NearCubicWires.InverseSelectorAtomStreamClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseSelectorAtomStreamClosure
open NearCubicWires.TotalInverseSelectorAtomStreamSourceBank
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenAtomStreamContract
open NearCubicWires.TotalSelectorDrivenBodyAdapterRuns
open NearCubicWires.TotalStructuralAtomCalleeProgram
open NearCubicWires.TotalStructuralAtomRangeProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private contextSwapProgram run_contextSwapProgram from
  Proof.MachineModel.BankAtomContextRegisters
open private inverseSelectorAdapterFrame_fixedTarget from
  Proof.Circuits.InverseSelectorAtomStreamClosure

set_option maxHeartbeats 1600000 in
-- The proof composes the source bank and three dependent guarded stages.
/-- The concrete guarded selector atom stream runs for every target. -/
theorem totalInverseDescriptionAtomStreamTotalRuns_ofSelectorCompiler
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
    TotalInverseDescriptionAtomStreamRuns contracts clockDepth machine
      advantageExponent
      (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorAtomStreamBits contracts clockDepth machine
        advantageExponent pcp rangeBits compilerBits)
      (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) := by
  intro target
  let sourceIndex :=
    BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
      advantageExponent target
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
  rw [hsourceLen] at hbank
  have hadapterRuns := totalInverseSelectorBodyAdapterTotalRuns contracts
    clockDepth machine advantageExponent pcp hpresentation compilerBits
    compilerFuel hcompiler
  have hadapter := hadapterRuns ⟨target, fixedTargetCodeInput target⟩
  simp only [LanguageEvaluationRequest.length] at hadapter
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
      width = inverseFrameWidth contracts clockDepth advantageExponent target :=
    by rfl
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

end NearCubicWires.TotalSelectorDrivenAtomStreamRuns

import Proof.Circuits.SelectorDrivenEmitterRuns
import Proof.MachineModel.TotalBankEmittedAtomLoop
import Proof.Circuits.TotalSelectorDrivenEmitterResources
import Proof.MachineModel.TotalStructuralAtomEmitterProgram

/-!
# The guarded atom emitter at the selector-driven frame

This is the selector-frame twin of `totalInverseEmitterRuns_ofCompiler`.
The retained frame and adapter ABI are unchanged; only the structural emitter
program and compiler contract are replaced by their total guarded versions.
-/

namespace NearCubicWires.TotalSelectorDrivenEmitterRuns

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenEmitterRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TotalStructuralAtomEmitterProgram

set_option maxHeartbeats 1600000 in
-- The dependent total emitter resources expand the full scheduled compiler ABI.
theorem totalInverseSelectorEmitterRuns_ofCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hatoms :
      InverseScheduleAtomsAgree contracts clockDepth machine advantageExponent
        pcp)
    (adapter : NPOracleProgram)
    (adapterBits adapterFuel : LanguageEvaluationRequest → ℕ)
    (rangeBits : ℕ → ℕ) (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hadapter :
      InverseSelectorFrameAdapterRuns contracts clockDepth machine
        advantageExponent pcp adapter adapterBits adapterFuel)
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
    InverseSelectorEmitterRuns contracts clockDepth machine advantageExponent
      (totalInverseBankEmitterProgram adapter)
      (totalInverseSelectorBankEmitterBits contracts clockDepth machine
        advantageExponent pcp adapterBits rangeBits)
      (totalInverseBankEmitterFuel contracts clockDepth machine
        advantageExponent pcp adapterFuel compilerFuel) := by
  intro target hlarge input
  have hloop :=
    run_totalStructuralAtomEmitterProgram_ofCompiler pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target
      (inverseScheduleBound contracts clockDepth advantageExponent target)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        ⟨target, input⟩)
      (compilerBits target) (compilerFuel target) (hpositive target)
      (hlengthBits target) (hrangeBits target) (hlistBits target)
      (hcallBits target) (hcalleeBits target) (hcompiler target)
  rw [hatoms target] at hloop
  exact run_occurrenceStage (hadapter target hlarge input) hloop

end NearCubicWires.TotalSelectorDrivenEmitterRuns

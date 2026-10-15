import Proof.Circuits.TotalSelectorDrivenEmitterTotalContract
import Proof.Circuits.TotalSelectorDrivenBodyAdapterRuns
import Proof.MachineModel.TotalBankEmittedAtomLoop
import Proof.MachineModel.TotalStructuralAtomEmitterProgram

/-! # All-request guarded selector emitter run -/

namespace NearCubicWires.TotalSelectorDrivenEmitterTotalRuns

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
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectorDrivenContextContracts
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TotalSelectorDrivenEmitterTotalContract
open NearCubicWires.TotalStructuralAtomEmitterProgram

set_option maxRecDepth 2000 in
-- The dependent emitter output normalizes a deeply nested tagged atom list.
set_option maxHeartbeats 1600000 in
-- The dependent total emitter resources expand the scheduled compiler ABI.
/-- A total selector-frame adapter followed by the guarded structural emitter
is total for every request. -/
theorem totalInverseSelectorEmitterTotalRuns_ofCompiler
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
      TotalInverseSelectorFrameAdapterRuns contracts clockDepth machine
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
    TotalInverseSelectorEmitterRuns contracts clockDepth machine
      advantageExponent (totalInverseBankEmitterProgram adapter)
      (totalInverseSelectorBankEmitterBits contracts clockDepth machine
        advantageExponent pcp adapterBits rangeBits)
      (totalInverseBankEmitterFuel contracts clockDepth machine
        advantageExponent pcp adapterFuel compilerFuel) := by
  intro request
  have hloop :=
    run_totalStructuralAtomEmitterProgram_ofCompiler pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        request.length)
      request.length
      (inverseScheduleBound contracts clockDepth advantageExponent
        request.length)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (compilerBits request.length) (compilerFuel request.length)
      (hpositive request.length) (hlengthBits request.length)
      (hrangeBits request.length) (hlistBits request.length)
      (hcallBits request.length) (hcalleeBits request.length)
      (hcompiler request.length)
  rw [hatoms request.length] at hloop
  exact run_occurrenceStage (hadapter request) hloop

end NearCubicWires.TotalSelectorDrivenEmitterTotalRuns

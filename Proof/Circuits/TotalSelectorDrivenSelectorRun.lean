import Proof.Circuits.SelectorDrivenTotalRunContract
import Proof.Circuits.SelectorDrivenBodyDispatch
import Proof.Circuits.TotalSelectorDrivenEmitterResources
import Proof.Circuits.TotalSelectorDrivenEmitterTotalContract
import Proof.Circuits.TotalSelectorDrivenSelectorResources

/-!
# Total branch selection from an all-request guarded emitter

The theorem is purely an ABI adapter. It turns an atom emitter that runs at
every selector frame into a Boolean selector run at every request. No onset or
semantic branch premise occurs.
-/

namespace NearCubicWires.TotalSelectorDrivenSelectorRun

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyDispatch
open NearCubicWires.SelectorDrivenTotalRunContract
open NearCubicWires.ScheduledRecovery
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TotalSelectorDrivenEmitterTotalContract
open NearCubicWires.TotalSelectorDrivenSelectorResources

set_option maxHeartbeats 800000 in
-- The scheduled bounded-oracle formula is definitionally the emitted atom list.
theorem selectorTotalRunsAtFrame_of_totalEmitter
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitter : NPOracleProgram)
    (emitterBits emitterFuel : LanguageEvaluationRequest → ℕ)
    (hemitter :
      TotalInverseSelectorEmitterRuns contracts clockDepth machine
        advantageExponent emitter emitterBits emitterFuel) :
    SelectorTotalRunsAtFrame (emittedBranchSelectorProgram emitter)
      (inverseBankSelectorBitsAtFrame contracts clockDepth machine
        advantageExponent
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
        emitterBits)
      (inverseBankSelectorFuel contracts clockDepth machine advantageExponent
        emitterFuel)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent) := by
  intro request
  let tag :=
    (encodedSat
      (boundedOracleRecoveryCode
        (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          request.length)
        (inverseScheduleBound contracts clockDepth advantageExponent
          request.length))).toNat
  have htag : tag ≤ 1 := by
    unfold tag
    cases encodedSat
        (boundedOracleRecoveryCode
          (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            request.length)
          (inverseScheduleBound contracts clockDepth advantageExponent
            request.length)) <;>
      simp
  refine ⟨tag, htag, ?_⟩
  have hrun := run_emittedBranchSelectorProgram
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseScheduleInput contracts clockDepth machine advantageExponent
      request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent request.length)
    request.length
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent request)
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent request)
    (emitterBits request) (emitterFuel request) emitter
    (by simpa only [inverseSelectorAtoms_eq] using hemitter request)
  rw [inverseBankSelectorBitsAtFrame_eq_schedule,
    inverseBankSelectorFuel_eq_schedule]
  change _ = some (Nat.pair tag _)
  exact hrun

end NearCubicWires.TotalSelectorDrivenSelectorRun

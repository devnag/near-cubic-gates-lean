import Proof.Circuits.SelectorDrivenTotalRunContract
import Proof.Circuits.TotalSelectorDrivenEmitterResources

/-! # All-request guarded emitter contract at the selector frame -/

namespace NearCubicWires.TotalSelectorDrivenEmitterTotalContract

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns

/-- The guarded atom emitter at the selector frame, universally quantified
over requests rather than restricted to the semantic onset. -/
def TotalInverseSelectorEmitterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (emitter : NPOracleProgram)
    (emitterBits emitterFuel : LanguageEvaluationRequest → ℕ) : Prop :=
  ∀ request : LanguageEvaluationRequest,
    runNPOracleProgram emitter (emitterBits request) (emitterFuel request)
        (initialNPOracleState request.length
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)) =
      some
        (Nat.pair
          (encodeTaggedList
            (inverseSelectorAtoms contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent request.length))
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request))

end NearCubicWires.TotalSelectorDrivenEmitterTotalContract

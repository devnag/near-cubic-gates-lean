import Proof.Circuits.TotalInverseSelectorAtomStreamClosure

/-! # All-request guarded description atom-stream contract -/

namespace NearCubicWires.TotalSelectorDrivenAtomStreamContract

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter

/-- The guarded description atom stream at every public target, including
zero.  This is the totality counterpart of the onset-indexed semantic ABI. -/
def TotalInverseDescriptionAtomStreamRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (stream : NPOracleProgram) (streamBits streamFuel : ℕ → ℕ) : Prop :=
  ∀ target : ℕ,
    runNPOracleProgram stream (streamBits target) (streamFuel target)
        (initialNPOracleState target target) =
      some
        (descriptionFrameSource
          (inverseFrameAtoms contracts clockDepth machine advantageExponent
            target)
          (inverseFrameWidth contracts clockDepth advantageExponent target)
          (inverseFrameBound contracts clockDepth advantageExponent target))

end NearCubicWires.TotalSelectorDrivenAtomStreamContract

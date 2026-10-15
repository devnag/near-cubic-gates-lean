import Proof.Circuits.InverseSelectorNativeWidth

/-!
# The inverse substitution request's three-field tail

Pairs the selector-scheduled native width with the already closed scheduled
source length/refuter-word stream.  All three fields are computed from the
public `(target,target)` state without a schedule diagonal.
-/

namespace NearCubicWires.InverseSubstitutionRequestTail

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorNativeWidth
open NearCubicWires.InverseSelectorRequestSourceAdapter
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.VerifiedLinker

noncomputable def inverseSubstitutionRequestTailProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) : NPOracleProgram :=
  occurrencePacketPairProgram
    (inverseSelectorNativeWidthProgram contracts clockDepth advantageExponent)
    (inverseTailSourceWordProgram contracts clockDepth machine
      advantageExponent)

noncomputable def inverseSubstitutionRequestTailBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrencePacketPairBits target
    (inverseSelectorNativeWidthBits contracts clockDepth advantageExponent
      target)
    (inverseTailSourceWordBits contracts clockDepth machine advantageExponent
      target)
    ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
      (inverseTailSourceLength contracts clockDepth advantageExponent target))
    (Nat.pair
      (inverseTailSourceLength contracts clockDepth advantageExponent target)
      (inverseTailRefuterCode contracts clockDepth machine advantageExponent
        target))

noncomputable def inverseSubstitutionRequestTailFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrencePacketPairFuel
    (inverseSelectorNativeWidthProgram contracts clockDepth advantageExponent)
    (inverseTailSourceWordProgram contracts clockDepth machine
      advantageExponent)
    (inverseSelectorNativeWidthFuel contracts clockDepth advantageExponent
      target)
    (inverseTailSourceWordFuel contracts clockDepth machine advantageExponent
      target)

set_option maxHeartbeats 800000 in
-- The two streams expose dependent scheduled source and refuter fields.
theorem run_inverseSubstitutionRequestTailProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) :
    runNPOracleProgram
        (inverseSubstitutionRequestTailProgram contracts clockDepth machine
          advantageExponent)
        (inverseSubstitutionRequestTailBits contracts clockDepth machine
          advantageExponent target)
        (inverseSubstitutionRequestTailFuel contracts clockDepth machine
          advantageExponent target)
        (initialNPOracleState target target) =
      some
        (Nat.pair
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.nativeWidth
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target))
          (Nat.pair
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target)
            (inverseTailRefuterCode contracts clockDepth machine
              advantageExponent target))) := by
  exact run_occurrencePacketPairProgram
    (inverseSelectorNativeWidthProgram contracts clockDepth advantageExponent)
    (inverseTailSourceWordProgram contracts clockDepth machine advantageExponent)
    target
    (inverseSelectorNativeWidthBits contracts clockDepth advantageExponent
      target)
    (inverseSelectorNativeWidthFuel contracts clockDepth advantageExponent
      target)
    (inverseTailSourceWordBits contracts clockDepth machine advantageExponent
      target)
    (inverseTailSourceWordFuel contracts clockDepth machine advantageExponent
      target)
    _ _
    (run_inverseSelectorNativeWidthProgram contracts clockDepth
      advantageExponent target)
    (run_inverseTailSourceWordProgram contracts clockDepth machine
      advantageExponent target)

end NearCubicWires.InverseSubstitutionRequestTail

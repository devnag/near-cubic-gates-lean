import Proof.Circuits.FixedTotalScheduledRowStageClosure
import Proof.CaseAnalysis.SelectorDrivenRegisterCaseOneChain

/-!
# The inverse scheduled row without query-count positivity

The total row emitter is schedule-agnostic.  Specializing it at the inverse
source index gives `InverseScheduledRowRuns` for every query count, including
zero.  Together with the direct selector-register Case-one theorem, this
removes both the old positivity premise and the old schedule diagonal.
-/

namespace NearCubicWires.InverseTotalScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedTotalScheduledRowStageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalOuterProofRowGuardedProgram

noncomputable def inverseTotalScheduledRowProgram
    (contracts : PublishedContracts) (clockDepth : ℕ) : NPOracleProgram :=
  totalOuterProofRowProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp

noncomputable def inverseTotalScheduledRowBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target code : ℕ) : ℕ :=
  totalOuterProofRowGuardBits
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
        advantageExponent target))
    code

noncomputable def inverseTotalScheduledRowFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target code : ℕ) : ℕ :=
  totalOuterProofRowFuel
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)
    code

set_option maxHeartbeats 800000 in
-- The inverse source index occurs dependently in the input word and output row.
theorem run_inverseTotalScheduledRowProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target code : ℕ) :
    runNPOracleProgram (inverseTotalScheduledRowProgram contracts clockDepth)
        (inverseTotalScheduledRowBits contracts clockDepth machine
          advantageExponent target code)
        (inverseTotalScheduledRowFuel contracts clockDepth machine
          advantageExponent target code)
        (initialNPOracleState
          (sourceLength
            (BankRegisterCaseOneChain.inverseChainSourceIndex contracts
              clockDepth advantageExponent target))
          (Nat.pair code
            (Nat.pair
              (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
                (BankRegisterCaseOneChain.inverseChainSourceIndex contracts
                  clockDepth advantageExponent target))
              (encodeBitInput
                (inverseRefuterInput contracts
                  (publishedHierarchyOuterPCP contracts clockDepth) machine
                  advantageExponent target))))) =
      some
        (encodeTaggedList
          (outerProofRowStream
            (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
            (inverseRefuterInput contracts
              (publishedHierarchyOuterPCP contracts clockDepth) machine
              advantageExponent target)
            code)) := by
  have hrun := run_totalOuterProofRowProgram
    (publishedHierarchyOuterPCP contracts clockDepth).pcp
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)
    (scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
      (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
        advantageExponent target))
    code
  have hout := totalOuterProofRowOutput_eq_scheduled
    (publishedHierarchyOuterPCP contracts clockDepth)
    (BankRegisterCaseOneChain.inverseChainSourceIndex contracts clockDepth
      advantageExponent target)
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)
    code
  unfold inverseTotalScheduledRowProgram inverseTotalScheduledRowBits
    inverseTotalScheduledRowFuel
  exact hrun.trans (congrArg some hout)

theorem inverseTotalScheduledRowRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) :
    InverseScheduledRowRuns contracts clockDepth machine advantageExponent
      (inverseTotalScheduledRowProgram contracts clockDepth)
      (inverseTotalScheduledRowBits contracts clockDepth machine
        advantageExponent)
      (inverseTotalScheduledRowFuel contracts clockDepth machine
        advantageExponent) := by
  intro target _hlarge code _hcode
  exact run_inverseTotalScheduledRowProgram contracts clockDepth machine
    advantageExponent target code

end NearCubicWires.InverseTotalScheduledRowStageClosure

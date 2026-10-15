import Proof.MachineModel.BankScheduledRowStageClosure
import Proof.CaseAnalysis.FixedRegisterCaseOneChain

/-!
# The fixed schedule's decision-row residual

The published scheduled row program is schedule-independent.  This module
instantiates its source index and refuter input at the fixed schedule, reducing
`FixedScheduledRowRuns` to the same honest query-count positivity condition as
the inverse schedule.  No diagonal is involved.
-/

namespace NearCubicWires.FixedScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedRegisterCaseOneChain
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRowStageProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

noncomputable def fixedScheduledRowProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) : NPOracleProgram :=
  inverseScheduledRowProgram contracts clockDepth

theorem fixedScheduledRowProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    OracleFree (fixedScheduledRowProgram contracts clockDepth) :=
  inverseScheduledRowProgram_oracleFree contracts clockDepth

noncomputable def fixedScheduledRowBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (target code : ℕ) : ℕ :=
  outerProofRowScheduledBits (publishedHierarchyOuterPCP contracts clockDepth)
    (fixedChainSourceIndex contracts clockDepth requestedRate target)
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    code

noncomputable def fixedScheduledRowFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (target code : ℕ) : ℕ :=
  outerProofRowScheduledFuel (publishedHierarchyOuterPCP contracts clockDepth)
    (fixedChainSourceIndex contracts clockDepth requestedRate target)
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    code

/-- Positivity of the query count at every fixed scheduled source length. -/
def FixedScheduledQueryCounts (contracts : PublishedContracts)
    (clockDepth requestedRate : ℕ) : Prop :=
  ∀ target : ℕ,
    0 <
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength
          (fixedChainSourceIndex contracts clockDepth requestedRate target))

/-- The fixed scheduled row is executed by the published row program from the
query-count side condition alone. -/
theorem fixedScheduledRowRuns_ofQueryCounts
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (requestedRate : ℕ)
    (hcounts : FixedScheduledQueryCounts contracts clockDepth requestedRate) :
    FixedScheduledRowRuns contracts clockDepth machine requestedRate
      (fixedScheduledRowProgram contracts clockDepth)
      (fixedScheduledRowBits contracts clockDepth machine requestedRate)
      (fixedScheduledRowFuel contracts clockDepth machine requestedRate) := by
  intro target _hlarge code _hcode
  exact run_outerProofRowScheduledProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (fixedChainSourceIndex contracts clockDepth requestedRate target)
    (fixedRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine requestedRate
      target)
    code (hcounts target)

end NearCubicWires.FixedScheduledRowStageClosure

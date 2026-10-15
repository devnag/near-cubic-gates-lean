import Proof.MachineModel.BankRegisterCaseOneChain

/-!
# The Case-1 chain's row residual, discharged

`BankRegisterCaseOneChain` left exactly one premise, `InverseScheduledRowRuns`:
one decision-row stage that, at the schedule's own source index and public
length, emits the padded decision row of every requested randomness code.
`OuterProofRowStageProgram.outerProofRowScheduledProgram` is now such a stage
*uniformly in the target*, so the premise is discharged by quoting its run.

## Why the stage is target uniform

The row stage used to carry two immediates, the scheduled native width and the
scheduled query count, both chosen from the requested target.  Neither is
recoverable from the row's input frame: the `width` that frame carries is
`RecoveryScheduleEnvelope.scheduledWidth`, i.e. the *envelope*
`ProjectionWidthEnvelope.widthEnvelope`, which `nativeWidth_le_widthEnvelope`
bounds the native width by but does not equal it.

Both numerals are, however, the two components of one published object:
`ExecutableProjectionPCP.nativeWidth` and `ExecutableProjectionPCP.queryCount`
are the left and right halves of `ExecutableProjectionPCP.shapeCode`, and that
code is produced by the published shape runner `pcp.shape` from the public
length alone.  `VerifiedLinker.linkPrograms` preserves register one — the
public length — through every stage, so each stage of the row that needs a
numeral reloads the length, runs the published shape program and unpairs.  No
frame above the row changes shape, and no numeral remains an immediate.

## What is left

Only the scheduled query-count positivity, which
`BranchTargetLanguageProgram` already documents as unavailable from the
published interface — `ExecutableProjectionPCPGuarantee` bounds `queryCount`
from above only — and therefore carries as an explicit hypothesis on the
Case-1 branch.  It is carried here in exactly the same way.
-/

namespace NearCubicWires.BankScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRowStageProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The scheduled row stage and its envelopes -/

/-- **The decision-row stage of the published hierarchy PCP.**  One fixed
instruction stream: the published query, decision and shape runners, and
nothing chosen from the request. -/
noncomputable def inverseScheduledRowProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) : NPOracleProgram :=
  outerProofRowScheduledProgram
    (publishedHierarchyOuterPCP contracts clockDepth)

theorem inverseScheduledRowProgram_oracleFree
    (contracts : PublishedContracts) (clockDepth : ℕ) :
    OracleFree (inverseScheduledRowProgram contracts clockDepth) :=
  outerProofRowScheduledProgram_oracleFree
    (publishedHierarchyOuterPCP contracts clockDepth)

/-- Width of the row stage at one target and randomness code. -/
noncomputable def inverseScheduledRowBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target code : ℕ) : ℕ :=
  outerProofRowScheduledBits (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseChainSourceIndex contracts clockDepth advantageExponent target)
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target) code

/-- Fuel of the row stage at one target and randomness code. -/
noncomputable def inverseScheduledRowFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (target code : ℕ) : ℕ :=
  outerProofRowScheduledFuel (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseChainSourceIndex contracts clockDepth advantageExponent target)
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target) code

/-! ## 2. The scheduled query-count side condition -/

/-- The one side condition of the decision row: at each scheduled length the
published PCP asks at least one query.  With no query the address fold has no
first coordinate and the emitted row is not the padded one; the published
interface bounds `queryCount` only from above, so this is carried, never
derived. -/
def InverseScheduledQueryCounts (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ) : Prop :=
  ∀ target : ℕ,
    0 <
      (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
        (sourceLength
          (inverseChainSourceIndex contracts clockDepth advantageExponent
            target))

/-! ## 3. `InverseScheduledRowRuns`, discharged -/

/-- **The Case-1 chain's row residual, discharged.**  The published decision
row stage runs at every target above the Case-1 onset and every randomness code
below the scheduled width, emitting exactly the padded decision row the Case-1
recovery seed consumes.  The entry length is arbitrary in the sense that it is
the schedule's own source length, the two envelopes are functions of the
request alone, and the schedule diagonal is neither used nor asserted here. -/
theorem inverseScheduledRowRuns_ofQueryCounts
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (hcounts :
      InverseScheduledQueryCounts contracts clockDepth advantageExponent) :
    InverseScheduledRowRuns contracts clockDepth machine advantageExponent
      (inverseScheduledRowProgram contracts clockDepth)
      (inverseScheduledRowBits contracts clockDepth machine advantageExponent)
      (inverseScheduledRowFuel contracts clockDepth machine
        advantageExponent) := by
  intro target _hlarge code _hcode
  exact run_outerProofRowScheduledProgram
    (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseChainSourceIndex contracts clockDepth advantageExponent target)
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target) code (hcounts target)

end NearCubicWires.BankScheduledRowStageClosure

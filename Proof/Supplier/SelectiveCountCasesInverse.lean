import Proof.MachineModel.BankEmittedAtomLoop
import Proof.Supplier.SelectiveFixedCountRun

/-!
# The compiler premise of the inverse schedule, from the fixed-count level

`BankEmittedAtomLoop.inverse_bodyRun_ofCompiler` consumes `InverseCompilerRuns`:
the nested structural compiler's run on its own ABI frame at every target and
every global formula index.  `SelectiveCountCasesRun.run_selectiveCountCasesProgram`
executes that compiler's outermost controller from one named level premise, the
fixed-count sub-compiler's own run.  This module carries the reduction across
the schedule: a fixed-count runner at each target discharges
`InverseCompilerRuns` outright, together with the two resource envelopes it is
consumed at.
-/

namespace NearCubicWires.SelectiveCountCasesInverse

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram

/-- **The pointwise compiler premise, from the fixed-count level.**  A
fixed-count runner at one PCP input and one bounded-oracle size bound
discharges `StructuralCompilerRunsAt` at every global formula index, at the
resource envelopes the controller's own proof constructs. -/
theorem structuralCompilerRunsAt_of_fixedCountRunner
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound index : ℕ)
    (runner :
      SelectiveFixedCountRunner (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound) :
    StructuralCompilerRunsAt pcp input machineInputLength bound index
      (selectiveCountCasesRunBits (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound runner index)
      (selectiveCountCasesRunFuel (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound runner index) :=
  run_selectiveCountCasesProgram (projectionRunnerCallOutputs pcp input)
    (pcp.nativeWidth n) (pcp.queryCount n) bound runner machineInputLength index

/-- Register width of one nested-compiler run at one scheduled target. -/
noncomputable def inverseFixedCountCompilerBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (runners : ∀ target : ℕ,
      SelectiveFixedCountRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
    (target index : ℕ) : ℕ :=
  selectiveCountCasesRunBits _ _ _ _ (runners target) index

/-- Interpreter fuel of one nested-compiler run at one scheduled target. -/
noncomputable def inverseFixedCountCompilerFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (runners : ∀ target : ℕ,
      SelectiveFixedCountRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
    (target index : ℕ) : ℕ :=
  selectiveCountCasesRunFuel _ _ _ _ (runners target) index

/-- **`InverseCompilerRuns` from the fixed-count level.**  One fixed-count
runner per scheduled target discharges the entire compiler premise of
`BankEmittedAtomLoop.inverse_bodyRun_ofCompiler`. -/
theorem inverseCompilerRuns_of_fixedCountRunners
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (runners : ∀ target : ℕ,
      SelectiveFixedCountRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target)) :
    InverseCompilerRuns contracts clockDepth executable advantageExponent pcp
      (inverseFixedCountCompilerBits contracts clockDepth executable
        advantageExponent pcp runners)
      (inverseFixedCountCompilerFuel contracts clockDepth executable
        advantageExponent pcp runners) := by
  intro target index _
  exact structuralCompilerRunsAt_of_fixedCountRunner pcp
    (inverseScheduleInput contracts clockDepth executable advantageExponent
      target)
    target (inverseScheduleBound contracts clockDepth advantageExponent target)
    index (runners target)

/-- **`InverseCompilerRuns` from the two levels below the fixed-count level.**
One grammar runner and one verifier-row runner per scheduled target discharge
the entire compiler premise of `BankEmittedAtomLoop.inverse_bodyRun_ofCompiler`,
with no obligation left at either the outermost controller or the fixed-count
level. -/
theorem inverseCompilerRuns_of_fixedCountLevels
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (grammarRunners : ∀ target : ℕ,
      SelectiveFixedCountGrammarRunner
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
    (rowsRunners : ∀ target : ℕ,
      SelectiveVerifierRowsRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target)) :
    InverseCompilerRuns contracts clockDepth executable advantageExponent pcp
      (inverseFixedCountCompilerBits contracts clockDepth executable
        advantageExponent pcp
        (fun target =>
          selectiveFixedCountRunnerOfLevels _ _ _ _ (grammarRunners target)
            (rowsRunners target)))
      (inverseFixedCountCompilerFuel contracts clockDepth executable
        advantageExponent pcp
        (fun target =>
          selectiveFixedCountRunnerOfLevels _ _ _ _ (grammarRunners target)
            (rowsRunners target))) :=
  inverseCompilerRuns_of_fixedCountRunners contracts clockDepth executable
    advantageExponent pcp
    (fun target =>
      selectiveFixedCountRunnerOfLevels _ _ _ _ (grammarRunners target)
        (rowsRunners target))

end NearCubicWires.SelectiveCountCasesInverse

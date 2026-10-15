import Proof.MachineModel.BankEmittedAtomLoop
import Proof.MachineModel.TotalStructuralAtomCalleeProgram

/-!
# The guarded inverse-schedule compiler proposition

This is the program-parametric analogue of `InverseCompilerRuns`.  Its target
and index schedule is identical, but the pointwise proposition records the
compiler program.  The guarded specialization therefore covers query arity
zero and malformed raw clause encodings through the total compiler stream.
-/

namespace NearCubicWires.TotalBankEmittedAtomLoop

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalSelectiveFixedCountProgram
open NearCubicWires.TotalStructuralAtomCalleeProgram

/-- The inverse schedule's compiler-run proposition with program ownership
exposed. -/
def InverseCompilerProgramRuns
    (compilerProgram : NPOracleProgram)
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits compilerFuel : ℕ → ℕ → ℕ) : Prop :=
  ∀ target index,
    index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target →
    StructuralCompilerProgramRunsAt compilerProgram pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target (inverseScheduleBound contracts clockDepth advantageExponent target)
      index (compilerBits target index) (compilerFuel target index)

/-- The schedule proposition for the total guarded count-cases compiler. -/
def TotalInverseCompilerRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits compilerFuel : ℕ → ℕ → ℕ) : Prop :=
  InverseCompilerProgramRuns totalSelectiveCountCasesProgram contracts
    clockDepth machine advantageExponent pcp compilerBits compilerFuel

/-! ## A schedule-level supplier from guarded fixed-count runners -/

noncomputable def totalInverseFixedCountCompilerBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (runners : ∀ target,
      SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
    (target index : ℕ) : ℕ :=
  selectiveCountCasesRunBits _ _ _ _ (runners target) index

noncomputable def totalInverseFixedCountCompilerFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (runners : ∀ target,
      SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
    (target index : ℕ) : ℕ :=
  selectiveCountCasesRunFuel _ _ _ _ (runners target) index

/-- A guarded fixed-count runner at each scheduled target supplies the exact
`InverseCompilerRuns`-shaped total proposition, without query-count
positivity. -/
theorem totalInverseCompilerRuns_of_fixedCountProgramRunners
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (runners : ∀ target,
      SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target)) :
    TotalInverseCompilerRuns contracts clockDepth machine advantageExponent pcp
      (totalInverseFixedCountCompilerBits contracts clockDepth machine
        advantageExponent pcp runners)
      (totalInverseFixedCountCompilerFuel contracts clockDepth machine
        advantageExponent pcp runners) := by
  intro target index _
  exact structuralCompilerProgramRunsAt_total pcp
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)
    target (inverseScheduleBound contracts clockDepth advantageExponent target)
    index (runners target)

end NearCubicWires.TotalBankEmittedAtomLoop

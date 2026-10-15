import Proof.Supplier.SelectiveClausesLevelRun
import Proof.Supplier.SelectiveTowerClosure
import Proof.PCP.PaddedProjectionPresentation

namespace NearCubicWires.SelectiveCountCasesInverse

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram

/-- **The address evaluator at every scheduled target.**  No premise. -/
noncomputable def inverseTowerAddressRunners (contracts : PublishedContracts)
    (clockDepth : ℕ) (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    StructuralAddressRunner
      (projectionRunnerCallOutputs pcp
        (inverseScheduleInput contracts clockDepth executable advantageExponent
          target))
      (pcp.nativeWidth
        (inverseScheduleLength contracts clockDepth advantageExponent target)) :=
  structuralAddressRunner _ _

/-- **The clause-list compiler at every scheduled target.**  The only premise is
the row's own query-count positivity. -/
noncomputable def inverseTowerClausesRunners (contracts : PublishedContracts)
    (clockDepth : ℕ) (_executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hqueryCount : ∀ target : ℕ,
      0 <
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
    (target : ℕ) :
    SelectiveClausesRunner
      (descriptionWidth
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
      (pcp.queryCount
        (inverseScheduleLength contracts clockDepth advantageExponent target)) :=
  selectiveClausesRunner _ _ (hqueryCount target)

/-! ## 2. The compiler premise, closed -/

/-- Register width of one closed nested-compiler run at one scheduled target. -/
noncomputable def inverseClosedCompilerBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hqueryCount : ∀ target : ℕ,
      0 <
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
    (target index : ℕ) : ℕ :=
  inverseTowerCompilerBits contracts clockDepth executable advantageExponent pcp
    (inverseTowerAddressRunners contracts clockDepth executable
      advantageExponent pcp)
    (inverseTowerClausesRunners contracts clockDepth executable
      advantageExponent pcp hqueryCount)
    target index

/-- Interpreter fuel of one closed nested-compiler run at one scheduled
target. -/
noncomputable def inverseClosedCompilerFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hqueryCount : ∀ target : ℕ,
      0 <
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
    (target index : ℕ) : ℕ :=
  inverseTowerCompilerFuel contracts clockDepth executable advantageExponent pcp
    (inverseTowerAddressRunners contracts clockDepth executable
      advantageExponent pcp)
    (inverseTowerClausesRunners contracts clockDepth executable
      advantageExponent pcp hqueryCount)
    target index

/-- **`InverseCompilerRuns`, closed.**  Every level of the nested structural
compiler's sixteen-level tower now executes on the machine at every scheduled
target: the compiler premise of `BankEmittedAtomLoop.inverse_bodyRun_ofCompiler`
holds for *any* presented projection PCP whose scheduled rows carry at least one
query, with no caller-supplied runner, callback or fuel. -/
theorem inverseCompilerRuns_closed (contracts : PublishedContracts)
    (clockDepth : ℕ) (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hqueryCount : ∀ target : ℕ,
      0 <
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)) :
    InverseCompilerRuns contracts clockDepth executable advantageExponent pcp
      (inverseClosedCompilerBits contracts clockDepth executable
        advantageExponent pcp hqueryCount)
      (inverseClosedCompilerFuel contracts clockDepth executable
        advantageExponent pcp hqueryCount) :=
  inverseCompilerRuns_of_clauseLeaves contracts clockDepth executable
    advantageExponent pcp
    (inverseTowerAddressRunners contracts clockDepth executable
      advantageExponent pcp)
    (inverseTowerClausesRunners contracts clockDepth executable
      advantageExponent pcp hqueryCount)

/-- The closed tower, packaged as the existential the atom-stream consumers
take: some register width and some interpreter clock make every nested-compiler
run succeed. -/
theorem exists_inverseCompilerRuns (contracts : PublishedContracts)
    (clockDepth : ℕ) (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hqueryCount : ∀ target : ℕ,
      0 <
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)) :
    ∃ compilerBits compilerFuel : ℕ → ℕ → ℕ,
      InverseCompilerRuns contracts clockDepth executable advantageExponent pcp
        compilerBits compilerFuel :=
  ⟨_, _,
    inverseCompilerRuns_closed contracts clockDepth executable advantageExponent
      pcp hqueryCount⟩

/-- **The side condition in its published form.**  For a presented PCP the query
count is the published outer PCP's own, so the positivity premise above is
literally the side condition `BranchTargetLanguageProgram` already carries for
the scheduled Case-one chain — `0 < outer.pcp.queryCount (sourceLength …)` at
the same scheduled source index. -/
theorem exists_inverseCompilerRuns_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)
        pcp)
    (hqueryCount : ∀ target : ℕ,
      0 <
        (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)) :
    ∃ compilerBits compilerFuel : ℕ → ℕ → ℕ,
      InverseCompilerRuns contracts clockDepth executable advantageExponent pcp
        compilerBits compilerFuel := by
  refine exists_inverseCompilerRuns contracts clockDepth executable
    advantageExponent pcp ?_
  intro target
  rw [presentsPaddedOuterPCP_queryCount hpresentation]
  exact hqueryCount target

end NearCubicWires.SelectiveCountCasesInverse

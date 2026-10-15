import Proof.Circuits.StructuralAddressRun
import Proof.Supplier.SelectiveFixedCountGrammarRun
import Proof.Supplier.SelectiveTowerClosure
import Proof.Circuits.TotalInverseCompilerRuns
import Proof.MachineModel.TotalSelectiveClausesGuardedProgram
import Proof.MachineModel.TotalSelectiveFixedCountProgram
import Proof.MachineModel.TotalSelectiveVerifierRowsProgram

/-! # Premise-free canonical guarded inverse compiler runners -/

namespace NearCubicWires.TotalInverseCanonicalCompilerRuns

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectiveCountCasesInverse
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectiveClausesGuardedProgram
open NearCubicWires.TotalSelectiveFixedCountProgram
open NearCubicWires.TotalSelectiveVerifierRowsProgram

/-! ## 1. The four exact target-indexed runners -/

/-- The projection-table address evaluator at one inverse target. -/
noncomputable def totalInverseCanonicalAddressRunner
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    StructuralAddressRunner
      (projectionRunnerCallOutputs pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target))
      (pcp.nativeWidth
        (inverseScheduleLength contracts clockDepth advantageExponent target)) :=
  structuralAddressRunner _ _

/-- The guarded clause-list compiler at one inverse target, including query
arity zero. -/
noncomputable def totalInverseCanonicalClausesRunner
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (_machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    SelectiveClausesProgramRunner totalSelectiveClausesProgram
      (descriptionWidth
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target))
      (pcp.queryCount
        (inverseScheduleLength contracts clockDepth advantageExponent target)) :=
  totalSelectiveClausesRunner _ _

/-- The exact guarded verifier-row scheduler at one inverse target. -/
noncomputable def totalInverseCanonicalRowsRunner
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
      (projectionRunnerCallOutputs pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target))
      (pcp.nativeWidth
        (inverseScheduleLength contracts clockDepth advantageExponent target))
      (pcp.queryCount
        (inverseScheduleLength contracts clockDepth advantageExponent target))
      (inverseScheduleBound contracts clockDepth advantageExponent target) :=
  selectiveVerifierRowsRunnerOfLevels _ _
    (selectiveUniversalOutputsRunnerOfAddress _
      (totalInverseCanonicalAddressRunner contracts clockDepth machine
        advantageExponent pcp target))
    (totalInverseCanonicalClausesRunner contracts clockDepth machine
      advantageExponent pcp target)

/-- The exact guarded fixed-count runner consumed by the total count-cases
compiler at one inverse target. -/
noncomputable def totalInverseCanonicalFixedCountRunner
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      (projectionRunnerCallOutputs pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target))
      (pcp.nativeWidth
        (inverseScheduleLength contracts clockDepth advantageExponent target))
      (pcp.queryCount
        (inverseScheduleLength contracts clockDepth advantageExponent target))
      (inverseScheduleBound contracts clockDepth advantageExponent target) :=
  selectiveFixedCountRunnerOfLevels _ _ _ _
    (selectiveFixedCountGrammarRunner _ _)
    (totalInverseCanonicalRowsRunner contracts clockDepth machine
      advantageExponent pcp target)

/-! ## 2. Exact compiler resources and total schedule run -/

/-- Register width of the canonical total inverse compiler. -/
noncomputable def totalInverseCanonicalCompilerBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  totalInverseFixedCountCompilerBits contracts clockDepth machine
    advantageExponent pcp
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp)
    target index

/-- Interpreter fuel of the canonical total inverse compiler. -/
noncomputable def totalInverseCanonicalCompilerFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  totalInverseFixedCountCompilerFuel contracts clockDepth machine
    advantageExponent pcp
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp)
    target index

/-- The canonical guarded compiler executes at every inverse target and every
live structural atom index.  There is no query-count or runner premise. -/
theorem totalInverseCanonicalCompilerRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) :
    TotalInverseCompilerRuns contracts clockDepth machine advantageExponent pcp
      (totalInverseCanonicalCompilerBits contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalCompilerFuel contracts clockDepth machine
        advantageExponent pcp) :=
  totalInverseCompilerRuns_of_fixedCountProgramRunners contracts clockDepth
    machine advantageExponent pcp
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp)

end NearCubicWires.TotalInverseCanonicalCompilerRuns

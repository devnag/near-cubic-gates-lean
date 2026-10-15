import Proof.Supplier.SelectiveCountCasesInverse
import Proof.Supplier.SelectiveFixedCountGrammarRun
import Proof.Supplier.SelectiveVerifierRowsRun

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

/-! ## 1. The address selector's block bound

Every description row is six tag bits and two field blocks of the same limit, so
the second field block always fits. -/

theorem selectiveAddressBlock (width bound : ℕ) :
    6 + boundedCircuitFieldLimit width bound ≤ rowWidth width bound := by
  unfold rowWidth
  omega

/-- **The projected query compiler, from the address evaluator alone.** -/
noncomputable def selectiveUniversalOutputsRunnerOfAddress {width bound : ℕ}
    (outputs : List ℕ)
    (addressRunner : StructuralAddressRunner outputs width) :
    SelectiveUniversalOutputsRunner outputs width bound :=
  selectiveUniversalOutputsRunnerOfLevels outputs
    (selectiveUniversalOutputRunnerOfLevels
      (selectiveUniversalNodeRunnerOfLevels
        (selectiveFieldSelectRunner width bound)
        (selectiveAddressSelectRunner width bound
          (selectiveAddressBlock width bound)))
      (selectiveFieldSelectRunner width bound))
    addressRunner

noncomputable def selectiveVerifierRowsRunnerOfLeaves {width bound : ℕ}
    (outputs : List ℕ) (count : ℕ)
    (addressRunner : StructuralAddressRunner outputs width)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count) :
    SelectiveVerifierRowsRunner outputs width count bound :=
  selectiveVerifierRowsRunnerOfLevels outputs count
    (selectiveUniversalOutputsRunnerOfAddress outputs addressRunner)
    clausesRunner

/-! ## 3. The compiler premise of the inverse schedule -/

noncomputable def inverseTowerCompilerBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (addressRunners : ∀ target : ℕ,
      StructuralAddressRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)))
    (clausesRunners : ∀ target : ℕ,
      SelectiveClausesRunner
        (descriptionWidth
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)))
    (target index : ℕ) : ℕ :=
  inverseFixedCountCompilerBits contracts clockDepth executable
    advantageExponent pcp
    (fun target =>
      selectiveFixedCountRunnerOfLevels _ _ _ _
        (selectiveFixedCountGrammarRunner _ _)
        (selectiveVerifierRowsRunnerOfLeaves _ _ (addressRunners target)
          (clausesRunners target)))
    target index

noncomputable def inverseTowerCompilerFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (addressRunners : ∀ target : ℕ,
      StructuralAddressRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)))
    (clausesRunners : ∀ target : ℕ,
      SelectiveClausesRunner
        (descriptionWidth
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)))
    (target index : ℕ) : ℕ :=
  inverseFixedCountCompilerFuel contracts clockDepth executable
    advantageExponent pcp
    (fun target =>
      selectiveFixedCountRunnerOfLevels _ _ _ _
        (selectiveFixedCountGrammarRunner _ _)
        (selectiveVerifierRowsRunnerOfLeaves _ _ (addressRunners target)
          (clausesRunners target)))
    target index

theorem inverseCompilerRuns_of_clauseLeaves
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (executable : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (addressRunners : ∀ target : ℕ,
      StructuralAddressRunner
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth executable
            advantageExponent target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent
            target)))
    (clausesRunners : ∀ target : ℕ,
      SelectiveClausesRunner
        (descriptionWidth
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target))) :
    InverseCompilerRuns contracts clockDepth executable advantageExponent pcp
      (inverseTowerCompilerBits contracts clockDepth executable
        advantageExponent pcp addressRunners clausesRunners)
      (inverseTowerCompilerFuel contracts clockDepth executable
        advantageExponent pcp addressRunners clausesRunners) :=
  inverseCompilerRuns_of_fixedCountLevels contracts clockDepth executable
    advantageExponent pcp
    (fun _ => selectiveFixedCountGrammarRunner _ _)
    (fun target =>
      selectiveVerifierRowsRunnerOfLeaves _ _ (addressRunners target)
        (clausesRunners target))

end NearCubicWires.SelectiveCountCasesInverse

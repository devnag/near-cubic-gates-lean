import Proof.Circuits.TotalInverseCanonicalCompilerRuns
import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.TotalInverseCanonicalCompilerResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.ValidatorPolynomialDomination

open private selectiveCountCasesForwardBits selectiveCountCasesForwardFuel from
  Proof.MachineModel.TotalSelectiveCountCasesProgram

/-! ## 1. Definition-level census

The outer total compiler has exactly two resource heads.  Width is the maximum
of the request-code width and the recursive candidate walk.  Fuel is the
seventeen-instruction parser plus that same recursive walk.  The definitions
below expose those two heads at the exact canonical target-indexed runner. -/

private noncomputable def canonicalOutputs
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : List ℕ :=
  projectionRunnerCallOutputs pcp
    (inverseScheduleInput contracts clockDepth machine advantageExponent target)

private noncomputable def canonicalWidth
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  pcp.nativeWidth
    (inverseScheduleLength contracts clockDepth advantageExponent target)

private noncomputable def canonicalCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  pcp.queryCount
    (inverseScheduleLength contracts clockDepth advantageExponent target)

private noncomputable def canonicalBound
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  inverseScheduleBound contracts clockDepth advantageExponent target

/-- Width of the compiler's exact request-code head. -/
noncomputable def totalInverseCanonicalCompilerRequestBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  natBitLength
    (structuralCompilerCoreInput
      (canonicalOutputs contracts clockDepth machine advantageExponent pcp
        target)
      (canonicalWidth contracts clockDepth advantageExponent pcp target)
      (canonicalCount contracts clockDepth advantageExponent pcp target)
      (canonicalBound contracts clockDepth advantageExponent target) index)

/-- The first recursive width callee: the complete candidate walk begun at its
actual empty state, full candidate list, and empty spine. -/
noncomputable def totalInverseCanonicalCompilerForwardBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  let outputs := canonicalOutputs contracts clockDepth machine advantageExponent
    pcp target
  let width := canonicalWidth contracts clockDepth advantageExponent pcp target
  let count := canonicalCount contracts clockDepth advantageExponent pcp target
  let bound := canonicalBound contracts clockDepth advantageExponent target
  selectiveCountCasesForwardBits outputs width count bound
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp target)
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    (List.ofFn id) []

/-- The first recursive fuel callee at the same canonical initial state. -/
noncomputable def totalInverseCanonicalCompilerForwardFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  let outputs := canonicalOutputs contracts clockDepth machine advantageExponent
    pcp target
  let width := canonicalWidth contracts clockDepth advantageExponent pcp target
  let count := canonicalCount contracts clockDepth advantageExponent pcp target
  let bound := canonicalBound contracts clockDepth advantageExponent target
  selectiveCountCasesForwardFuel outputs width count bound
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp target)
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    (List.ofFn id) []

/-- Exact width census: no inequality and no correctness theorem is used. -/
theorem totalInverseCanonicalCompilerBits_eq_frontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerBits contracts clockDepth machine
        advantageExponent pcp target index =
      max
        (totalInverseCanonicalCompilerRequestBits contracts clockDepth machine
          advantageExponent pcp target index)
        (totalInverseCanonicalCompilerForwardBits contracts clockDepth machine
          advantageExponent pcp target index) := by
  rfl

/-- Exact fuel census: the only outer overhead is the parser's seventeen
steps. -/
theorem totalInverseCanonicalCompilerFuel_eq_frontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerFuel contracts clockDepth machine
        advantageExponent pcp target index =
      17 +
        totalInverseCanonicalCompilerForwardFuel contracts clockDepth machine
          advantageExponent pcp target index := by
  rfl

/-- The target-indexed domination shape used by every live compiler atom. -/
def CanonicalCompilerPolyBounded
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (charge : ℕ → ℕ → ℕ) (coefficient degree : ℕ) : Prop :=
  ∀ target index,
    index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target →
    PolyBounded (charge target index) (max 1 target) coefficient degree

/-- Width is polynomial once its exact request head and first recursive
candidate-walk callee are polynomial. -/
theorem totalInverseCanonicalCompilerBits_polyBounded_of_frontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (requestCoefficient forwardCoefficient degree : ℕ)
    (hrequest : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerRequestBits contracts clockDepth machine
        advantageExponent pcp) requestCoefficient degree)
    (hforward : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerForwardBits contracts clockDepth machine
        advantageExponent pcp) forwardCoefficient degree) :
    CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerBits contracts clockDepth machine
        advantageExponent pcp)
      (max requestCoefficient forwardCoefficient) degree := by
  intro target index hindex
  rw [totalInverseCanonicalCompilerBits_eq_frontier]
  exact (hrequest target index hindex).max (hforward target index hindex)

/-- Fuel is polynomial once its exact first recursive candidate-walk callee is
polynomial. -/
theorem totalInverseCanonicalCompilerFuel_polyBounded_of_frontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (forwardCoefficient degree : ℕ)
    (hforward : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerForwardFuel contracts clockDepth machine
        advantageExponent pcp) forwardCoefficient degree) :
    CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerFuel contracts clockDepth machine
        advantageExponent pcp)
      (17 + forwardCoefficient) degree := by
  intro target index hindex
  rw [totalInverseCanonicalCompilerFuel_eq_frontier]
  exact (polyBounded_const 17 (max 1 target) degree).add
    (hforward target index hindex)

end NearCubicWires.TotalInverseCanonicalCompilerResources

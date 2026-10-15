import Proof.Supplier.TotalInverseCanonicalFixedCountWalkResources

/-! # Nonrecursive domination interface for the fixed-count walk

The exact walk recurrences are reduced here to pointwise bounds on each call
they actually visit.  Width takes the pointwise maximum unchanged; fuel pays
the actual candidate count once.  This is the global-invariant interface used
instead of inducting on the dependent canonical `List.ofFn id` downstream.
-/

namespace NearCubicWires.TotalInverseCanonicalFixedCountWalkDomination

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.TotalInverseCanonicalCompilerForwardResources
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseCanonicalFixedCountWalkResources
open NearCubicWires.TotalSelectiveFixedCountProgram
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

/-! ## 1. Pointwise invariants over exactly the visited calls -/

def SelectiveFixedCountWalkBitsWithin (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (maximum : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → Prop
  | _, [] => True
  | state, candidate :: rest =>
      runner.bits state candidate ≤ maximum ∧
        SelectiveFixedCountWalkBitsWithin outputs width count bound runner
          maximum
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest

def SelectiveFixedCountWalkFuelWithin (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (maximum : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → Prop
  | _, [] => True
  | state, candidate :: rest =>
      runner.fuel state candidate ≤ maximum ∧
        SelectiveFixedCountWalkFuelWithin outputs width count bound runner
          maximum
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest

theorem selectiveFixedCountWalkBits_le_of_within
    (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (maximum : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound))
    (hwithin : SelectiveFixedCountWalkBitsWithin outputs width count bound
      runner maximum state candidates) :
    selectiveFixedCountWalkBits outputs width count bound runner state
        candidates ≤ maximum := by
  induction candidates generalizing state with
  | nil => simp [selectiveFixedCountWalkBits]
  | cons candidate rest ih =>
      simp only [SelectiveFixedCountWalkBitsWithin] at hwithin
      simp only [selectiveFixedCountWalkBits]
      exact max_le hwithin.1 (ih _ hwithin.2)

theorem selectiveFixedCountWalkFuel_le_of_within
    (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (maximum : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound))
    (hwithin : SelectiveFixedCountWalkFuelWithin outputs width count bound
      runner maximum state candidates) :
    selectiveFixedCountWalkFuel outputs width count bound runner state
        candidates ≤ candidates.length * maximum := by
  induction candidates generalizing state with
  | nil => simp [selectiveFixedCountWalkFuel]
  | cons candidate rest ih =>
      simp only [SelectiveFixedCountWalkFuelWithin] at hwithin
      simp only [selectiveFixedCountWalkFuel, List.length_cons]
      have hrest := ih _ hwithin.2
      nlinarith

/-! ## 2. Canonical live-call interfaces -/

def CanonicalFixedCountWalkBitsWithin
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (maximum : ℕ → ℕ → ℕ) : Prop :=
  ∀ target index,
    index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target →
    let outputs := canonicalOutputs contracts clockDepth machine
      advantageExponent pcp target
    let width := canonicalWidth contracts clockDepth advantageExponent pcp target
    let count := canonicalCount contracts clockDepth advantageExponent pcp target
    let bound := canonicalBound contracts clockDepth advantageExponent target
    SelectiveFixedCountWalkBitsWithin outputs width count bound
      (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
        advantageExponent pcp target)
      (maximum target index)
      (SelectiveState.empty (descriptionWidth width bound)
        (index - structuralInputArity width bound))
      (List.ofFn id)

def CanonicalFixedCountWalkFuelWithin
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (maximum : ℕ → ℕ → ℕ) : Prop :=
  ∀ target index,
    index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target →
    let outputs := canonicalOutputs contracts clockDepth machine
      advantageExponent pcp target
    let width := canonicalWidth contracts clockDepth advantageExponent pcp target
    let count := canonicalCount contracts clockDepth advantageExponent pcp target
    let bound := canonicalBound contracts clockDepth advantageExponent target
    SelectiveFixedCountWalkFuelWithin outputs width count bound
      (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
        advantageExponent pcp target)
      (maximum target index)
      (SelectiveState.empty (descriptionWidth width bound)
        (index - structuralInputArity width bound))
      (List.ofFn id)

/-! ## 3. Eliminate the recursive walk charges -/

theorem totalInverseCanonicalFixedCountWalkBits_dominated_of_callsWithin
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (maximum : ℕ → ℕ → ℕ) (coefficient degree : ℕ)
    (hwithin : CanonicalFixedCountWalkBitsWithin contracts clockDepth machine
      advantageExponent pcp maximum)
    (hmaximum : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp maximum coefficient degree) :
    CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerFixedCountWalkBits contracts clockDepth
        machine advantageExponent pcp)
      coefficient degree := by
  intro target index hindex
  exact (hmaximum target index hindex).mono <|
    selectiveFixedCountWalkBits_le_of_within _ _ _ _ _ _ _ _
      (hwithin target index hindex)

theorem totalInverseCanonicalFixedCountWalkFuel_dominated_of_callsWithin
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (maximum : ℕ → ℕ → ℕ)
    (maximumCoefficient boundCoefficient maximumDegree boundDegree : ℕ)
    (hwithin : CanonicalFixedCountWalkFuelWithin contracts clockDepth machine
      advantageExponent pcp maximum)
    (hmaximum : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp maximum maximumCoefficient maximumDegree)
    (hbound : ∀ target,
      PolyBounded
        (canonicalBound contracts clockDepth advantageExponent target)
        (max 1 target) boundCoefficient boundDegree) :
    CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
        machine advantageExponent pcp)
      (boundCoefficient * maximumCoefficient)
      (boundDegree + maximumDegree) := by
  intro target index hindex
  have hproduct := (hbound target).mul (hmaximum target index hindex)
  exact hproduct.mono <| by
    calc
      totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
          machine advantageExponent pcp target index ≤
        (List.ofFn
          (id : Fin
            (canonicalBound contracts clockDepth advantageExponent target) →
              Fin
                (canonicalBound contracts clockDepth advantageExponent target))).length *
          maximum target index :=
        selectiveFixedCountWalkFuel_le_of_within _ _ _ _ _ _ _ _
          (hwithin target index hindex)
      _ = canonicalBound contracts clockDepth advantageExponent target *
          maximum target index := by simp

end NearCubicWires.TotalInverseCanonicalFixedCountWalkDomination

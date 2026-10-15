import Proof.Circuits.TotalInverseCanonicalCompilerRequestResources

/-! # Exact candidate-walk resource split for the inverse compiler

The count-cases controller interleaves one recursive fixed-count compiler call
per candidate with local framing, spine retention, and a terminal reverse fold.
This module separates those two charges by exact identities.  It also closes
the local fuel arithmetically; the only recursive fuel residual is then the
sum of the actual fixed-count runner calls along the actual compiler trajectory.
-/

namespace NearCubicWires.TotalInverseCanonicalCompilerForwardResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalSelectiveFixedCountProgram
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

open private selectiveCountCasesForwardBits selectiveCountCasesForwardFuel from
  Proof.MachineModel.TotalSelectiveCountCasesProgram

/-! ## 1. Split the generic candidate walk at its recursive callee -/

/-- Maximum width of the fixed-count runner calls on one exact candidate
trajectory. -/
def selectiveFixedCountWalkBits (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      max (runner.bits state candidate)
        (selectiveFixedCountWalkBits outputs width count bound runner
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest)

/-- Sum of the fixed-count runner fuels on the same exact trajectory. -/
def selectiveFixedCountWalkFuel (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) → ℕ
  | _, [] => 0
  | state, candidate :: rest =>
      runner.fuel state candidate +
        selectiveFixedCountWalkFuel outputs width count bound runner
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest

/-- Every non-runner width in the forward controller: request framing,
compiled-wire retention, reverse-spine retention, and the terminal fold. -/
def selectiveCountCasesLocalForwardBits (outputs : List ℕ)
    (width count bound : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      List ℕ → ℕ
  | state, [], spine =>
      max
        (natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (.const false))))
        (max
          (natBitLength
            (Nat.pair 0 (selectiveWireCode (selectiveConst state false))))
          (natBitLength
            (TotalSelectiveCountCasesProgram.selectiveCountCasesFoldWorkBound
              (selectiveConst state false).state
              (selectiveConst state false).output spine)))
  | state, candidate :: rest, spine =>
      max
        (natBitLength
          (selectiveFixedCountInput (selectiveStateCode state)
            (encodeTaggedList outputs) (structuralInputArity width bound)
            (structuralRowWidth width bound) (width + bound + 1) width count
            bound candidate.val))
        (max
          (natBitLength
            (Nat.pair 0
              (selectiveWireCode
                (selectiveCompileTableFixedCount outputs width count bound
                  state candidate))))
          (max
            (natBitLength
              (TotalSelectiveCountCasesProgram.selectiveCountCasesSpineCode
                ((selectiveCompileTableFixedCount outputs width count bound
                    state candidate).output :: spine)))
            (selectiveCountCasesLocalForwardBits outputs width count bound
              (selectiveCompileTableFixedCount outputs width count bound state
                candidate).state rest
              ((selectiveCompileTableFixedCount outputs width count bound state
                  candidate).output :: spine))))

/-- Every non-runner fuel in the forward controller.  Candidate iterations
cost exactly `12 + 9 = 21`; the terminal retains its actual emit and fold
charges. -/
def selectiveCountCasesLocalForwardFuel (outputs : List ℕ)
    (width count bound : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      List ℕ → ℕ
  | state, [], spine =>
      9 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (4 +
            TotalSelectiveCountCasesProgram.selectiveCountCasesFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine))
  | state, candidate :: rest, spine =>
      21 +
        selectiveCountCasesLocalForwardFuel outputs width count bound
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest
          ((selectiveCompileTableFixedCount outputs width count bound state
              candidate).output :: spine)

private theorem selectiveCountCasesForwardBits_eq_split
    (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) (spine : List ℕ) :
    selectiveCountCasesForwardBits outputs width count bound runner state
        candidates spine =
      max
        (selectiveFixedCountWalkBits outputs width count bound runner state
          candidates)
        (selectiveCountCasesLocalForwardBits outputs width count bound state
          candidates spine) := by
  induction candidates generalizing state spine with
  | nil =>
      simp [selectiveCountCasesForwardBits, selectiveFixedCountWalkBits,
        selectiveCountCasesLocalForwardBits]
  | cons candidate rest ih =>
      simp only [selectiveCountCasesForwardBits,
        selectiveFixedCountWalkBits, selectiveCountCasesLocalForwardBits]
      rw [ih]
      ac_rfl

private theorem selectiveCountCasesForwardFuel_eq_split
    (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) (spine : List ℕ) :
    selectiveCountCasesForwardFuel outputs width count bound runner state
        candidates spine =
      selectiveFixedCountWalkFuel outputs width count bound runner state
          candidates +
        selectiveCountCasesLocalForwardFuel outputs width count bound state
          candidates spine := by
  induction candidates generalizing state spine with
  | nil =>
      simp [selectiveCountCasesForwardFuel, selectiveFixedCountWalkFuel,
        selectiveCountCasesLocalForwardFuel]
  | cons candidate rest ih =>
      simp only [selectiveCountCasesForwardFuel,
        selectiveFixedCountWalkFuel, selectiveCountCasesLocalForwardFuel]
      rw [ih]
      omega

/-! ## 2. Instantiate the split at the canonical inverse trajectory -/

/-- Exact maximum of the lower fixed-count compiler widths actually called by
one canonical outer compiler run. -/
noncomputable def totalInverseCanonicalCompilerFixedCountWalkBits
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
  selectiveFixedCountWalkBits outputs width count bound
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp target)
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    (List.ofFn id)

/-- Exact sum of the lower fixed-count compiler fuels on that trajectory. -/
noncomputable def totalInverseCanonicalCompilerFixedCountWalkFuel
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
  selectiveFixedCountWalkFuel outputs width count bound
    (totalInverseCanonicalFixedCountRunner contracts clockDepth machine
      advantageExponent pcp target)
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    (List.ofFn id)

/-- Exact non-runner width of the canonical candidate walk. -/
noncomputable def totalInverseCanonicalCompilerLocalForwardBits
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
  selectiveCountCasesLocalForwardBits outputs width count bound
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    (List.ofFn id) []

/-- Exact non-runner fuel of the canonical candidate walk. -/
noncomputable def totalInverseCanonicalCompilerLocalForwardFuel
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
  selectiveCountCasesLocalForwardFuel outputs width count bound
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    (List.ofFn id) []

/-- Exact width identity at the first lower recursive callee. -/
theorem totalInverseCanonicalCompilerForwardBits_eq_fixedCountFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerForwardBits contracts clockDepth machine
        advantageExponent pcp target index =
      max
        (totalInverseCanonicalCompilerFixedCountWalkBits contracts clockDepth
          machine advantageExponent pcp target index)
        (totalInverseCanonicalCompilerLocalForwardBits contracts clockDepth
          machine advantageExponent pcp target index) := by
  exact selectiveCountCasesForwardBits_eq_split _ _ _ _ _ _ _ _

/-- Exact fuel identity at the same lower recursive callee. -/
theorem totalInverseCanonicalCompilerForwardFuel_eq_fixedCountFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerForwardFuel contracts clockDepth machine
        advantageExponent pcp target index =
      totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
          machine advantageExponent pcp target index +
        totalInverseCanonicalCompilerLocalForwardFuel contracts clockDepth
          machine advantageExponent pcp target index := by
  exact selectiveCountCasesForwardFuel_eq_split _ _ _ _ _ _ _ _

/-! ## 3. The local fuel is closed by candidate count alone -/

private theorem selectiveEmitFuel_le_seventeen
    (remaining selectedCode : ℕ) :
    selectiveEmitFuel remaining selectedCode ≤ 17 := by
  unfold selectiveEmitFuel
  by_cases hselected : selectedCode = 0
  · simp only [hselected, ↓reduceIte]
    split <;> omega
  · simp only [hselected, ↓reduceIte]
    omega

private theorem selectiveCountCasesFoldFuel_le
    {n : ℕ} (state : SelectiveState n) (accumulated : ℕ)
    (spine : List ℕ) :
    TotalSelectiveCountCasesProgram.selectiveCountCasesFoldFuel state
        accumulated spine ≤
      35 * spine.length + 2 := by
  induction spine generalizing state accumulated with
  | nil => rfl
  | cons value rest ih =>
      simp only [TotalSelectiveCountCasesProgram.selectiveCountCasesFoldFuel,
        List.length_cons]
      have hemit := selectiveEmitFuel_le_seventeen
        (state.target - state.next) (selectiveSelectedCode state.selected)
      have hrest := ih
        (selectiveOr state value accumulated).state
        (selectiveOr state value accumulated).output
      omega

private theorem selectiveCountCasesLocalForwardFuel_le
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) (spine : List ℕ) :
    selectiveCountCasesLocalForwardFuel outputs width count bound state
        candidates spine ≤
      56 * candidates.length + 35 * spine.length + 32 := by
  induction candidates generalizing state spine with
  | nil =>
      simp only [selectiveCountCasesLocalForwardFuel, List.length_nil,
        Nat.mul_zero, Nat.zero_add]
      have hemit := selectiveEmitFuel_le_seventeen
        (state.target - state.next) (selectiveSelectedCode state.selected)
      have hfold := selectiveCountCasesFoldFuel_le
        (selectiveConst state false).state
        (selectiveConst state false).output spine
      omega
  | cons candidate rest ih =>
      simp only [selectiveCountCasesLocalForwardFuel, List.length_cons]
      have hrest := ih
        (selectiveCompileTableFixedCount outputs width count bound state
          candidate).state
        ((selectiveCompileTableFixedCount outputs width count bound state
          candidate).output :: spine)
      simp only [List.length_cons] at hrest
      omega

/-- The canonical local forward fuel is linear in the actual candidate bound. -/
theorem totalInverseCanonicalCompilerLocalForwardFuel_le
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalCompilerLocalForwardFuel contracts clockDepth machine
        advantageExponent pcp target index ≤
      56 * canonicalBound contracts clockDepth advantageExponent target + 32 := by
  unfold totalInverseCanonicalCompilerLocalForwardFuel
  simpa using selectiveCountCasesLocalForwardFuel_le
    (canonicalOutputs contracts clockDepth machine advantageExponent pcp target)
    (canonicalWidth contracts clockDepth advantageExponent pcp target)
    (canonicalCount contracts clockDepth advantageExponent pcp target)
    (canonicalBound contracts clockDepth advantageExponent target)
    (SelectiveState.empty
      (descriptionWidth
        (canonicalWidth contracts clockDepth advantageExponent pcp target)
        (canonicalBound contracts clockDepth advantageExponent target))
      (index -
        structuralInputArity
          (canonicalWidth contracts clockDepth advantageExponent pcp target)
          (canonicalBound contracts clockDepth advantageExponent target)))
    (List.ofFn id) []

/-! ## 4. Polynomial splices at the fixed-count walk -/

/-- Forward width is polynomial from the exact lower runner maximum and the
exact non-runner width. -/
theorem totalInverseCanonicalCompilerForwardBits_dominated_of_fixedCountFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hfixed : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFixedCountWalkBits contracts clockDepth
          machine advantageExponent pcp)
        coefficient degree)
    (hlocal : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerLocalForwardBits contracts clockDepth
          machine advantageExponent pcp)
        coefficient degree) :
    ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerForwardBits contracts clockDepth machine
          advantageExponent pcp)
        coefficient degree := by
  obtain ⟨fixedCoefficient, hfixed⟩ := hfixed
  obtain ⟨localCoefficient, hlocal⟩ := hlocal
  refine ⟨max fixedCoefficient localCoefficient, ?_⟩
  intro target index hindex
  rw [totalInverseCanonicalCompilerForwardBits_eq_fixedCountFrontier]
  exact (hfixed target index hindex).max (hlocal target index hindex)

/-- Forward fuel is polynomial from the exact lower runner sum and a polynomial
bound for the actual candidate count; the local controller/fold fuel is closed
internally. -/
theorem totalInverseCanonicalCompilerForwardFuel_dominated_of_fixedCountWalk
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hfixed : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
          machine advantageExponent pcp)
        coefficient degree)
    (hbound : ∃ coefficient, ∀ target,
      PolyBounded
        (canonicalBound contracts clockDepth advantageExponent target)
        (max 1 target) coefficient degree) :
    ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerForwardFuel contracts clockDepth machine
          advantageExponent pcp)
        coefficient degree := by
  obtain ⟨fixedCoefficient, hfixed⟩ := hfixed
  obtain ⟨boundCoefficient, hbound⟩ := hbound
  refine ⟨fixedCoefficient + (56 * boundCoefficient + 32), ?_⟩
  intro target index hindex
  rw [totalInverseCanonicalCompilerForwardFuel_eq_fixedCountFrontier]
  apply (hfixed target index hindex).add
  have hlocal :
      PolyBounded
        (56 * canonicalBound contracts clockDepth advantageExponent target + 32)
        (max 1 target) (56 * boundCoefficient + 32) degree :=
    (hbound target).const_mul 56 |>.add
      (polyBounded_const 32 (max 1 target) degree)
  exact hlocal.mono
    (totalInverseCanonicalCompilerLocalForwardFuel_le contracts clockDepth
      machine advantageExponent pcp target index)

end NearCubicWires.TotalInverseCanonicalCompilerForwardResources

import Proof.Supplier.TotalInverseCanonicalFixedCountWalkDomination

/-! # Nonrecursive domination interface for local forward width

The local width recurrence contains three frames per candidate and one
terminal emit/fold frame.  This module replaces that trajectory-shaped maximum
by a single invariant over exactly the visited states and spines.
-/

namespace NearCubicWires.TotalInverseCanonicalLocalForwardBitsDomination

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
open NearCubicWires.TotalInverseCanonicalCompilerForwardResources
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseCanonicalFixedCountWalkDomination
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

/-! ## 1. The exact nonrecursive width heads -/

def selectiveCountCasesLocalStepBits (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) (spine : List ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveFixedCountInput (selectiveStateCode state)
        (encodeTaggedList outputs) (structuralInputArity width bound)
        (structuralRowWidth width bound) (width + bound + 1) width count bound
        candidate.val))
    (max
      (natBitLength
        (Nat.pair 0
          (selectiveWireCode
            (selectiveCompileTableFixedCount outputs width count bound state
              candidate))))
      (natBitLength
        (TotalSelectiveCountCasesProgram.selectiveCountCasesSpineCode
          ((selectiveCompileTableFixedCount outputs width count bound state
              candidate).output :: spine))))

def selectiveCountCasesLocalTerminalBits (width bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (spine : List ℕ) : ℕ :=
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

def SelectiveCountCasesLocalForwardBitsWithin (outputs : List ℕ)
    (width count bound maximum : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      List ℕ → Prop
  | state, [], spine =>
      selectiveCountCasesLocalTerminalBits width bound state spine ≤ maximum
  | state, candidate :: rest, spine =>
      selectiveCountCasesLocalStepBits outputs width count bound state candidate
          spine ≤ maximum ∧
        SelectiveCountCasesLocalForwardBitsWithin outputs width count bound
          maximum
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state rest
          ((selectiveCompileTableFixedCount outputs width count bound state
              candidate).output :: spine)

theorem selectiveCountCasesLocalForwardBits_le_of_within
    (outputs : List ℕ) (width count bound maximum : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) (spine : List ℕ)
    (hwithin : SelectiveCountCasesLocalForwardBitsWithin outputs width count
      bound maximum state candidates spine) :
    selectiveCountCasesLocalForwardBits outputs width count bound state
        candidates spine ≤ maximum := by
  induction candidates generalizing state spine with
  | nil =>
      simpa [selectiveCountCasesLocalForwardBits,
        SelectiveCountCasesLocalForwardBitsWithin,
        selectiveCountCasesLocalTerminalBits] using hwithin
  | cons candidate rest ih =>
      simp only [SelectiveCountCasesLocalForwardBitsWithin] at hwithin
      simp only [selectiveCountCasesLocalForwardBits]
      simpa only [selectiveCountCasesLocalStepBits, max_assoc] using
        max_le hwithin.1 (ih _ _ hwithin.2)

/-! ## 2. Canonical invariant and polynomial splice -/

def CanonicalLocalForwardBitsWithin
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
    SelectiveCountCasesLocalForwardBitsWithin outputs width count bound
      (maximum target index)
      (SelectiveState.empty (descriptionWidth width bound)
        (index - structuralInputArity width bound))
      (List.ofFn id) []

theorem totalInverseCanonicalCompilerLocalForwardBits_dominated_of_within
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (maximum : ℕ → ℕ → ℕ) (coefficient degree : ℕ)
    (hwithin : CanonicalLocalForwardBitsWithin contracts clockDepth machine
      advantageExponent pcp maximum)
    (hmaximum : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp maximum coefficient degree) :
    CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerLocalForwardBits contracts clockDepth
        machine advantageExponent pcp)
      coefficient degree := by
  intro target index hindex
  exact (hmaximum target index hindex).mono <|
    selectiveCountCasesLocalForwardBits_le_of_within _ _ _ _ _ _ _ _
      (hwithin target index hindex)

end NearCubicWires.TotalInverseCanonicalLocalForwardBitsDomination

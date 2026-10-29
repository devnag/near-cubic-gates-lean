import StatementSupport

/-!
# The paper's theorems, as propositions

This module defines propositions; `MainStatement` is the paper's main theorem (`thm:main`), proved in
`MainTheorem.lean` from the
seven published statements. The others are not proved in this repository. The `E^NP` predicate uses the finite-control
multitape execution semantics, including a polynomial-time verifier for the oracle. The size measure is the top
multiplicity `W`, not the total number of wires.
-/

set_option autoImplicit false

namespace NearCubicGates.Target

open scoped BigOperators
open NearCubicWires

/-- Periodicity is required on the complete frame `[-W,W]`, including score
values the circuit does not attain. The representation is kept fixed. -/
def WeightedSymmetricCircuit.HasPeriod {n : ℕ}
    (C : WeightedSymmetricCircuit n) (m : ℕ) : Prop :=
  0 < m ∧ ∃ f : ZMod m → Bool,
    ∀ z : ℤ, z.natAbs ≤ C.topWeight → C.lookup z = f (z : ZMod m)

/-- Integer power budget for periodic lookups. This auxiliary definition is not a statement of the paper. -/
def PeriodicBudget (K n w : ℕ) : Prop :=
  (K * w * lambda n ^ 10) ^ 2 * mu n ^ 23 ≤ n ^ 6

def BoundaryBudget (K n w : ℕ) : Prop :=
  (K * w * mu n ^ 7) ^ 4 * lambda n ^ 25 ≤ n ^ 12

/-- Both period ranges refer to the same circuit representation. Integer
power comparisons avoid rounding fractional roots. -/
def EligiblePeriod {n : ℕ} (C : WeightedSymmetricCircuit n) : Prop :=
  (∃ m : ℕ, C.HasPeriod m ∧ m ^ 6 ≤ n) ∨
    (∃ p : ℕ, Nat.Prime p ∧ C.HasPeriod p ∧ p ^ 11 ≤ n ^ 2)

/-- Auxiliary proposition for periodic lookups, not stated in the paper and not proved in this repository.
One language is selected before all lengths, periods, lookup functions and circuits. -/
def PeriodicStatement : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ C : WeightedSymmetricCircuit n,
        EligiblePeriod C → PeriodicBudget K n C.topWeight →
          agreement C F < 1 / 2 + 1 / (lambda n : ℝ)

/-- The conclusion of `cor:main-boundary` at the same rational gap. -/
def BoundaryAt (gamma : ℚ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ C : WeightedSymmetricCircuit n,
        BoundaryBudget K n C.topWeight →
          agreement C F < 1 - (gamma : ℝ) / 5 + 1 / (lambda n : ℝ)

/-- Not proved in this repository: the unrestricted headline and boundary refinement,
sharing one gap constant; the languages may differ, as in `thm:main` and `thm:gadget-boundary`. -/
def MainAndBoundaryStatement : Prop :=
  ∃ gamma : ℚ, 0 < gamma ∧ gamma < 1 ∧ MainAt gamma ∧ BoundaryAt gamma

/-- Auxiliary proposition for periodic lookups with inverse-polylogarithmic advantage, not stated in the paper
and not proved in this repository. The floor is explicit. -/
noncomputable def PeriodicLogPowersStatement : Prop :=
  ∀ a : ℚ, 0 < a → ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ C : WeightedSymmetricCircuit n, EligiblePeriod C →
        C.topWeight ≤ ⌊(n : ℝ) ^ 3 /
          ((K : ℝ) * (lambda n : ℝ) ^ (6 + 4 * (a : ℝ)) *
            (mu n : ℝ) ^ ((23 : ℝ) / 2))⌋₊ →
        agreement C F < 1 / 2 + (lambda n : ℝ) ^ (-(a : ℝ))

/-- Auxiliary proposition for periodic lookups at every rational exponent below 3, not stated in the paper and
not proved in this repository. The language is chosen before the arbitrary fixed multiplier `A`. -/
noncomputable def PeriodicRationalPowerStatement : Prop :=
  ∀ delta : ℚ, 0 < delta → delta < 3 →
    ∃ K : ℕ, 0 < K ∧ ∃ F : Language, InENP F ∧
      ∀ A : ℝ, 0 < A → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ C : WeightedSymmetricCircuit n,
          EligiblePeriod C →
          (C.topWeight : ℝ) ≤ A * (n : ℝ) ^ (3 - (delta : ℝ)) →
          agreement C F < 1 / 2 + (n : ℝ) ^ (-(delta : ℝ) / 4) *
            (2 : ℝ) ^ (⌈Real.sqrt (lambda n : ℝ)⌉₊ + K * mu n)

end NearCubicGates.Target

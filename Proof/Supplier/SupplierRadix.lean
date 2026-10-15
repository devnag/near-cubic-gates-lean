import Proof.Supplier.SupplierList

/-!
# Exact modular-radix lookup

This module formalizes the total Boolean lookup used after list amplification.
The row is parity over every bounded digit tuple, so it remains a total Boolean
polynomial even on malformed inputs.  When each digit list is genuinely
one-hot, exactly one tuple survives and the row is the intended modular test.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierRadix

def exactDigitOneHot {digits populationBound : ℕ}
    (actual : Fin digits → Fin (populationBound + 1)) :
    Fin digits → Fin (populationBound + 1) → Bool :=
  fun digit candidate => decide (candidate = actual digit)

def digitTupleMatches {digits populationBound : ℕ}
    (oneHot : Fin digits → Fin (populationBound + 1) → Bool)
    (tuple : Fin digits → Fin (populationBound + 1)) : Bool :=
  decide (∀ digit, oneHot digit (tuple digit) = true)

def radixValue {digits populationBound : ℕ} (base : ℕ)
    (tuple : Fin digits → Fin (populationBound + 1)) : ℕ :=
  ∑ digit, base ^ digit.val * (tuple digit).val

def digitPopulation {Carrier : Type} [Fintype Carrier] {digits : ℕ}
    (digit : Carrier → Fin digits → ℕ) (active : Carrier → Bool)
    (place : Fin digits) : ℕ :=
  ∑ carrier, digit carrier place * (active carrier).toNat

/-- Exact integer radix identity.  Carries are not approximated or decoded
digitwise: the complete weighted score equals the radix recombination of the
unweighted digit populations. -/
theorem radixScore_eq_digitPopulations
    {Carrier : Type} [Fintype Carrier] {digits : ℕ}
    (base : ℕ) (coefficient : Carrier → ℕ)
    (digit : Carrier → Fin digits → ℕ)
    (active : Carrier → Bool)
    (hcoefficient : ∀ carrier,
      coefficient carrier =
        ∑ place, base ^ place.val * digit carrier place) :
    ∑ carrier, coefficient carrier * (active carrier).toNat =
      ∑ place, base ^ place.val *
        digitPopulation digit active place := by
  simp_rw [hcoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold digitPopulation
  apply Finset.sum_congr rfl
  intro place _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro carrier _
  ring

theorem digitPopulationOn_le
    {Carrier : Type} {digits base : ℕ} (active : Finset Carrier)
    (digit : Carrier → Fin digits → ℕ)
    (place : Fin digits)
    (hdigit : ∀ carrier ∈ active, digit carrier place < base) :
    ∑ carrier ∈ active, digit carrier place ≤ active.card * (base - 1) := by
  classical
  calc
    (∑ carrier ∈ active, digit carrier place) ≤
        ∑ _carrier ∈ active, (base - 1) := by
      exact Finset.sum_le_sum fun carrier hcarrier =>
        Nat.le_sub_one_of_lt (hdigit carrier hcarrier)
    _ = active.card * (base - 1) := by simp

def modularTupleAccepts {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (tuple : Fin digits → Fin (populationBound + 1)) : Bool :=
  decide ((offset + radixValue base tuple) % modulus = 0)

def boolParity {Index : Type} [Fintype Index] (value : Index → Bool) : Bool :=
  decide (Odd (∑ index, (value index).toNat))

theorem boolParity_exactSelector
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (actual : Index) (value : Index → Bool) :
    boolParity (fun candidate => decide (candidate = actual) && value candidate) =
      value actual := by
  classical
  unfold boolParity
  have hsum :
      (∑ candidate,
        ((decide (candidate = actual) && value candidate).toNat)) =
        (value actual).toNat := by
    calc
      (∑ candidate,
          ((decide (candidate = actual) && value candidate).toNat)) =
          (decide (actual = actual) && value actual).toNat := by
        apply Finset.sum_eq_single actual
        · intro candidate _ hcandidate
          simp [hcandidate]
        · simp
      _ = (value actual).toNat := by simp
  rw [hsum]
  cases value actual <;> simp

/-- Total lookup row.  Parity, rather than existential selection, is essential:
it is the evaluation of the manuscript's GF(2) sum on malformed lists too. -/
def modularRadixRow {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot : Fin digits → Fin (populationBound + 1) → Bool) : Bool :=
  boolParity fun tuple : Fin digits → Fin (populationBound + 1) =>
    digitTupleMatches oneHot tuple &&
      modularTupleAccepts modulus offset base tuple

theorem digitTupleMatches_exact {digits populationBound : ℕ}
    (actual tuple : Fin digits → Fin (populationBound + 1)) :
    digitTupleMatches (exactDigitOneHot actual) tuple =
      decide (tuple = actual) := by
  apply Bool.eq_iff_iff.mpr
  simp only [digitTupleMatches, exactDigitOneHot, decide_eq_true_eq]
  constructor
  · intro hequal
    funext digit
    exact hequal digit
  · rintro rfl digit
    rfl

theorem modularRadixRow_exact {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (actual : Fin digits → Fin (populationBound + 1)) :
    modularRadixRow modulus offset base (exactDigitOneHot actual) =
      modularTupleAccepts modulus offset base actual := by
  unfold modularRadixRow
  simp_rw [digitTupleMatches_exact actual]
  exact boolParity_exactSelector actual
    (modularTupleAccepts modulus offset base)

theorem modularRadixRow_exact_spec {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (actual : Fin digits → Fin (populationBound + 1)) :
    modularRadixRow modulus offset base (exactDigitOneHot actual) = true ↔
      (offset + radixValue base actual) % modulus = 0 := by
  rw [modularRadixRow_exact]
  simp [modularTupleAccepts]

/-- Production-facing form: any compiled coordinate family proved to be the
exact one-hot vector feeds the same total radix row, without introducing a
second lookup implementation. -/
theorem modularRadixRow_eq_of_oneHot
    {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot : Fin digits → Fin (populationBound + 1) → Bool)
    (actual : Fin digits → Fin (populationBound + 1))
    (honeHot : ∀ digit candidate,
      oneHot digit candidate = decide (candidate = actual digit)) :
    modularRadixRow modulus offset base oneHot =
      modularTupleAccepts modulus offset base actual := by
  have hequal : oneHot = exactDigitOneHot actual := by
    funext digit candidate
    exact honeHot digit candidate
  rw [hequal]
  exact modularRadixRow_exact modulus offset base actual

theorem modularRadixRow_spec_of_oneHot
    {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot : Fin digits → Fin (populationBound + 1) → Bool)
    (actual : Fin digits → Fin (populationBound + 1))
    (honeHot : ∀ digit candidate,
      oneHot digit candidate = decide (candidate = actual digit)) :
    modularRadixRow modulus offset base oneHot = true ↔
      (offset + radixValue base actual) % modulus = 0 := by
  rw [modularRadixRow_eq_of_oneHot
    modulus offset base oneHot actual honeHot]
  simp [modularTupleAccepts]

/-- Multiplying one selected indicator per digit adds, rather than multiplies,
the list-output degrees. -/
theorem radixTuple_degree_le
    {digits : ℕ} (digitDegree : Fin digits → ℕ) (bound : ℕ)
    (hdegree : ∀ digit, digitDegree digit ≤ bound) :
    ∑ digit, digitDegree digit ≤ digits * bound := by
  calc
    (∑ digit, digitDegree digit) ≤ ∑ _digit : Fin digits, bound :=
      Finset.sum_le_sum fun digit _ => hdegree digit
    _ = digits * bound := by simp

end NearCubicWires.SupplierRadix

import Proof.Gates.PairReconstruction
import Proof.Gates.ResidueCounts
import Mathlib.Data.Fin.VecNotation

/-! Literal modular integer measurements, an accepted rational inverse, and
    exact arbitrary lookups on the same finite pair-score cell. This is the
    finite correctness layer; it asserts no saved running time. -/

set_option autoImplicit false

namespace NearCubicGates.PairCellCounter

open scoped BigOperators Matrix
open Reconstruction ResidueCounts FiniteDistributions ScalarWindow TomographyDirections

variable {Points : Type*} [Fintype Points] {L : ℕ}

def multiplicities (index : Points → Fin L × Fin L) : Fin L × Fin L → ℚ :=
  pushforward index (fun _ => 1)

def rawMeasurement (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (index : Points → Fin L × Fin L)
    (exponent : primes → ℕ) (row : PairResidueRow (fun p : primes => p.val)) : ℤ :=
  ∑ x : Points, liftedIndicator row.1.val (exponent row.1)
    ![lo₁ + ((index x).1.val : ℤ), lo₂ + ((index x).2.val : ℤ)]
    ![(row.2.1.val : ℤ), (row.2.2.val : ℤ)]

def measuredData (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (index : Points → Fin L × Fin L)
    (exponent : primes → ℕ) : PairResidueRow (fun p : primes => p.val) → ℚ :=
  fun row => ((rawMeasurement primes lo₁ lo₂ index exponent row %
    (row.1.val : ℤ) ^ exponent row.1 : ℤ) : ℚ)

theorem rawMeasurement_exact (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p) (lo₁ lo₂ : ℤ) (index : Points → Fin L × Fin L)
    (exponent : primes → ℕ) (he : ∀ p, 1 ≤ exponent p)
    (hsize : ∀ p, Fintype.card Points < p.val ^ exponent p)
    (row : PairResidueRow (fun p : primes => p.val)) :
    rawMeasurement primes lo₁ lo₂ index exponent row % (row.1.val : ℤ) ^ exponent row.1 =
      ((Finset.univ.filter (fun x : Points =>
        (lo₁ + ((index x).1.val : ℤ)) % (row.1.val : ℤ) = (row.2.1.val : ℤ) ∧
        (lo₂ + ((index x).2.val : ℤ)) % (row.1.val : ℤ) = (row.2.2.val : ℤ))).card : ℤ) := by
  have h := exact_joint_residue_count row.1.val (hprime _ row.1.property)
    (exponent row.1) (he row.1)
    (fun x : Points => ![lo₁ + ((index x).1.val : ℤ), lo₂ + ((index x).2.val : ℤ)])
    ![(row.2.1.val : ℤ), (row.2.2.val : ℤ)] (hsize row.1)
  simpa only [rawMeasurement, Int.ModEq, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ row.2.1.val)
      (by exact_mod_cast row.2.1.isLt : (row.2.1.val : ℤ) < (row.1.val : ℤ)),
    Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ row.2.2.val)
      (by exact_mod_cast row.2.2.isLt : (row.2.2.val : ℤ) < (row.1.val : ℤ))] using h

theorem matrix_measurements_exact (primes : Finset ℕ) (lo₁ lo₂ : ℤ)
    (index : Points → Fin L × Fin L) (row : PairResidueRow (fun p : primes => p.val)) :
    (pairMatrix primes lo₁ lo₂ L *ᵥ multiplicities index) row =
      ((Finset.univ.filter (fun x : Points =>
        (lo₁ + ((index x).1.val : ℤ)) % (row.1.val : ℤ) = (row.2.1.val : ℤ) ∧
        (lo₂ + ((index x).2.val : ℤ)) % (row.1.val : ℤ) = (row.2.2.val : ℤ))).card : ℚ) := by
  classical
  rw [← Finset.sum_boole]
  simp only [pairMatrix, pairResidueMatrix, Matrix.mulVec, dotProduct,
    multiplicities, pushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (index x)]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem measuredData_correct (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p) (lo₁ lo₂ : ℤ) (index : Points → Fin L × Fin L)
    (exponent : primes → ℕ) (he : ∀ p, 1 ≤ exponent p)
    (hsize : ∀ p, Fintype.card Points < p.val ^ exponent p) :
    measuredData primes lo₁ lo₂ index exponent = pairMatrix primes lo₁ lo₂ L *ᵥ multiplicities index := by
  funext row
  rw [measuredData, rawMeasurement_exact primes hprime lo₁ lo₂ index exponent he hsize,
    matrix_measurements_exact]
  simp

theorem multiplicity_statistic (index : Points → Fin L × Fin L) (lookup : Fin L × Fin L → ℚ) :
    (∑ j, lookup j * multiplicities index j) = ∑ x : Points, lookup (index x) := by
  classical
  simp only [multiplicities, pushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (index x)]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

def countWithInverse (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (index : Points → Fin L × Fin L)
    (exponent : primes → ℕ)
    (B : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ)
    (lookup : Fin L × Fin L → ℚ) : ℚ :=
  ∑ j, lookup j * (B *ᵥ measuredData primes lo₁ lo₂ index exponent) j

theorem countWithInverse_correct (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p) (lo₁ lo₂ : ℤ) (index : Points → Fin L × Fin L)
    (exponent : primes → ℕ) (he : ∀ p, 1 ≤ exponent p)
    (hsize : ∀ p, Fintype.card Points < p.val ^ exponent p)
    (B : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ)
    (hB : leftInverseCheck (pairMatrix primes lo₁ lo₂ L) B = true)
    (lookup : Fin L × Fin L → ℚ) :
    countWithInverse primes lo₁ lo₂ index exponent B lookup = ∑ x : Points, lookup (index x) := by
  unfold countWithInverse
  rw [measuredData_correct primes hprime lo₁ lo₂ index exponent he hsize,
    reconstruct_exact _ B hB]
  exact multiplicity_statistic index lookup

theorem pair_cell_counter_complete (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (hL : 2 ≤ L)
    (hwindow : L ≤ degreeSum ((window primes - 1) / (L - 1)))
    (exponent : primes → ℕ) (he : ∀ p, 1 ≤ exponent p)
    (hsize : ∀ p, Fintype.card Points < p.val ^ exponent p) :
    ∃ B : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (pairMatrix primes lo₁ lo₂ L) B = true ∧
      ∀ (index : Points → Fin L × Fin L) (lookup : Fin L × Fin L → ℚ),
        countWithInverse primes lo₁ lo₂ index exponent B lookup = ∑ x : Points, lookup (index x) := by
  obtain ⟨B, hB⟩ := pair_inverse_exists primes hne hprime lo₁ lo₂ L hL hwindow
  exact ⟨B, hB, fun index lookup =>
    countWithInverse_correct primes hprime lo₁ lo₂ index exponent he hsize B hB lookup⟩

end NearCubicGates.PairCellCounter

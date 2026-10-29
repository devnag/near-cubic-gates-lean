import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Sigma

/-!
# Certified finite reconstruction

This module formalizes the soundness of exact rational reconstruction after a
left inverse has been supplied and checked. It also defines the actual one-
and two-score residue push-forward matrices.

This module alone does **not** prove that a left inverse exists at the
windows of `lem:one-window` and `lem:two-window`; existence is proved in `ScalarReconstruction.lean` and
`TwoScoreWindow.lean`. A failed inverse check
establishes nothing.
The checker provides a concrete finite certificate, rather than an axiom
asserting injectivity of the residue map.
-/

namespace NearCubicGates.Reconstruction

open scoped BigOperators Matrix

section Certificates

variable {Rows Cols : Type*} [Fintype Rows] [Fintype Cols] [DecidableEq Cols]

/-- Check every entry of the proposed left-inverse identity over exact rationals. -/
def leftInverseCheck (A : Matrix Rows Cols ℚ) (B : Matrix Cols Rows ℚ) : Bool :=
  decide (∀ i j, (B * A) i j = (1 : Matrix Cols Cols ℚ) i j)

theorem checked_left_inverse (A : Matrix Rows Cols ℚ) (B : Matrix Cols Rows ℚ)
    (checked : leftInverseCheck A B = true) : B * A = 1 := by
  have entries : ∀ i j, (B * A) i j = (1 : Matrix Cols Cols ℚ) i j :=
    of_decide_eq_true checked
  funext i j
  exact entries i j

/-- Applying the certified inverse to exact measurement data recovers all masses. -/
theorem reconstruct_exact (A : Matrix Rows Cols ℚ) (B : Matrix Cols Rows ℚ)
    (checked : leftInverseCheck A B = true) (mass : Cols → ℚ) :
    B *ᵥ (A *ᵥ mass) = mass := by
  rw [Matrix.mulVec_mulVec, checked_left_inverse A B checked, Matrix.one_mulVec]

/-- Two histograms with identical measured data must be equal after a successful check. -/
theorem measurements_injective (A : Matrix Rows Cols ℚ) (B : Matrix Cols Rows ℚ)
    (checked : leftInverseCheck A B = true) :
    Function.Injective (fun mass : Cols → ℚ => A *ᵥ mass) := by
  intro mass₁ mass₂ sameData
  calc
    mass₁ = B *ᵥ (A *ᵥ mass₁) := (reconstruct_exact A B checked mass₁).symm
    _ = B *ᵥ (A *ᵥ mass₂) := congrArg (fun v => B *ᵥ v) sameData
    _ = mass₂ := reconstruct_exact A B checked mass₂

/-- Every solution of the equations equals the certified reconstruction.
This is a soundness statement for solving the finite rational system. -/
theorem any_solution_eq_reconstruction
    (A : Matrix Rows Cols ℚ) (B : Matrix Cols Rows ℚ)
    (checked : leftInverseCheck A B = true)
    (data : Rows → ℚ) (candidate : Cols → ℚ)
    (satisfies : A *ᵥ candidate = data) : candidate = B *ᵥ data := by
  calc
    candidate = B *ᵥ (A *ᵥ candidate) := (reconstruct_exact A B checked candidate).symm
    _ = B *ᵥ data := congrArg (fun v => B *ᵥ v) satisfies

/-- Every finite rational statistic, including a Boolean lookup expectation,
is preserved by successful reconstruction. -/
theorem reconstructed_statistic
    (A : Matrix Rows Cols ℚ) (B : Matrix Cols Rows ℚ)
    (checked : leftInverseCheck A B = true)
    (mass value : Cols → ℚ) :
    (∑ c, value c * (B *ᵥ (A *ᵥ mass)) c) = ∑ c, value c * mass c := by
  rw [reconstruct_exact A B checked mass]

end Certificates

section ResidueMatrices

variable {Columns Moduli : Type*} [Fintype Columns] [Fintype Moduli]

/-- Each measurement row chooses a modulus and one residue. -/
abbrev ResidueRow (modulus : Moduli → ℕ) := Σ m, Fin (modulus m)

/-- Each measurement row chooses a modulus and a pair of residues. -/
abbrev PairResidueRow (modulus : Moduli → ℕ) :=
  Σ m, Fin (modulus m) × Fin (modulus m)

/-- The actual scalar residue push-forward matrix; no primality is assumed here. -/
def residueMatrix (score : Columns → ℤ) (modulus : Moduli → ℕ) :
    Matrix (ResidueRow modulus) Columns ℚ :=
  fun row c => if score c % (modulus row.1 : ℤ) = (row.2.val : ℤ) then 1 else 0

/-- The actual joint two-score push-forward matrix. Both residues use the same modulus. -/
def pairResidueMatrix (score₁ score₂ : Columns → ℤ) (modulus : Moduli → ℕ) :
    Matrix (PairResidueRow modulus) Columns ℚ :=
  fun row c =>
    if score₁ c % (modulus row.1 : ℤ) = (row.2.1.val : ℤ) ∧
        score₂ c % (modulus row.1 : ℤ) = (row.2.2.val : ℤ) then 1 else 0

omit [Fintype Moduli] in
theorem residue_matrix_is_pushforward
    (score : Columns → ℤ) (modulus : Moduli → ℕ)
    (mass : Columns → ℚ) (row : ResidueRow modulus) :
    (residueMatrix score modulus *ᵥ mass) row =
      ∑ c ∈ Finset.univ.filter
        (fun c => score c % (modulus row.1 : ℤ) = (row.2.val : ℤ)), mass c := by
  simp [Matrix.mulVec, dotProduct, residueMatrix, Finset.sum_filter, ite_mul]

omit [Fintype Moduli] in
theorem pair_residue_matrix_is_pushforward
    (score₁ score₂ : Columns → ℤ) (modulus : Moduli → ℕ)
    (mass : Columns → ℚ) (row : PairResidueRow modulus) :
    (pairResidueMatrix score₁ score₂ modulus *ᵥ mass) row =
      ∑ c ∈ Finset.univ.filter
        (fun c => score₁ c % (modulus row.1 : ℤ) = (row.2.1.val : ℤ) ∧
          score₂ c % (modulus row.1 : ℤ) = (row.2.2.val : ℤ)), mass c := by
  simp [Matrix.mulVec, dotProduct, pairResidueMatrix, Finset.sum_filter, ite_mul]

/-- Certified two-score tomography on a supplied finite frame. The inverse check
is explicit; this theorem does not establish when such a check can succeed. -/
theorem certified_pair_residue_reconstruction [DecidableEq Columns]
    (score₁ score₂ : Columns → ℤ) (modulus : Moduli → ℕ)
    (B : Matrix Columns (PairResidueRow modulus) ℚ)
    (checked : leftInverseCheck (pairResidueMatrix score₁ score₂ modulus) B = true)
    (mass : Columns → ℚ) :
    B *ᵥ (pairResidueMatrix score₁ score₂ modulus *ᵥ mass) = mass :=
  reconstruct_exact (pairResidueMatrix score₁ score₂ modulus) B checked mass

end ResidueMatrices

end NearCubicGates.Reconstruction

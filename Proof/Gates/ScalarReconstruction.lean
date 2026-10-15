import Proof.Gates.ScalarWindow
import Proof.Gates.Reconstruction
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Existence and soundness of exact scalar reconstruction

The actual prime-residue matrix has a rational checked left inverse at the
manuscript's scalar window. No injectivity or inverse-existence axiom is used.
Existence here is algebraic. This module does not claim a running-time bound
for Gaussian elimination or a circuit-counting machine.
-/

namespace NearCubicGates.Reconstruction

open scoped BigOperators Matrix
open NearCubicGates.ScalarWindow

/-- Every injective finite rational measurement matrix has a certificate that
the existing exact-rational checker accepts. -/
theorem exists_checked_left_inverse {Rows Cols : Type*}
    [Fintype Rows] [Fintype Cols] [DecidableEq Rows] [DecidableEq Cols]
    (A : Matrix Rows Cols ℚ)
    (hinj : Function.Injective (fun mass : Cols → ℚ => A *ᵥ mass)) :
    ∃ B : Matrix Cols Rows ℚ, leftInverseCheck A B = true := by
  have hk : LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) hk
  have hm := congrArg
    (fun f : (Cols → ℚ) →ₗ[ℚ] (Cols → ℚ) => LinearMap.toMatrix' f) hg
  have hB : LinearMap.toMatrix' g * A = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using hm
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  simp [leftInverseCheck, hB]

/-- Rows really are one residue per prime, with columns at the actual signed
integer scores in the translated frame. -/
def scalarMatrix (primes : Finset ℕ) (lo : ℤ) (L : ℕ) :
    Matrix (ResidueRow (fun p : primes => p.val)) (Fin L) ℚ :=
  residueMatrix (fun i : Fin L => lo + (i.val : ℤ)) (fun p : primes => p.val)

theorem scalarMatrix_mulVec (primes : Finset ℕ) (lo : ℤ) (L : ℕ)
    (mass : Fin L → ℚ) (p : primes) (r : Fin p.val) :
    (scalarMatrix primes lo L *ᵥ mass) ⟨p, r⟩ =
      frameResidueData mass lo p.val (r.val : ℤ) := by
  simp [scalarMatrix, Matrix.mulVec, dotProduct, residueMatrix,
    frameResidueData, ite_mul]

/-- Proved injectivity of the actual residue matrix on the scalar window. -/
theorem scalarMatrix_injective (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo : ℤ) (L : ℕ) (hL : L ≤ window primes) :
    Function.Injective (fun mass : Fin L → ℚ => scalarMatrix primes lo L *ᵥ mass) := by
  intro a b hab
  apply residueData_injective primes hne hprime hL
  intro p hp r hr
  let s : ℤ := (lo + (r : ℤ)) % (p : ℤ)
  have hs0 : 0 ≤ s := Int.emod_nonneg _ (by exact_mod_cast (hprime p hp).ne_zero)
  have hsp : s < (p : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast (hprime p hp).pos)
  have hsn : s.toNat < p := by omega
  let row : ResidueRow (fun p : primes => p.val) := ⟨⟨p, hp⟩, ⟨s.toNat, hsn⟩⟩
  have hrow := congrFun hab row
  dsimp only [row] at hrow
  rw [scalarMatrix_mulVec, scalarMatrix_mulVec] at hrow
  have hs : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
  change frameResidueData a lo p (s.toNat : ℤ) =
    frameResidueData b lo p (s.toNat : ℤ) at hrow
  rw [hs] at hrow
  simpa only [s, frameResidueData_eq a lo p r hr,
    frameResidueData_eq b lo p r hr] using hrow

/-- Completeness of scalar inverse certificates, now with no supplied inverse
or injectivity hypothesis. -/
theorem scalar_inverse_exists (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo : ℤ) (L : ℕ) (hL : L ≤ window primes) :
    ∃ B : Matrix (Fin L) (ResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (scalarMatrix primes lo L) B = true := by
  classical
  exact exists_checked_left_inverse (scalarMatrix primes lo L)
    (scalarMatrix_injective primes hne hprime lo L hL)

/-- Every valid set of scalar measurements admits exact, simultaneous recovery
of all signed rational masses by an accepted finite certificate. -/
theorem scalar_reconstruction_complete (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo : ℤ) (L : ℕ) (hL : L ≤ window primes) :
    ∃ B : Matrix (Fin L) (ResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (scalarMatrix primes lo L) B = true ∧
      ∀ mass : Fin L → ℚ, B *ᵥ (scalarMatrix primes lo L *ᵥ mass) = mass := by
  obtain ⟨B, hB⟩ := scalar_inverse_exists primes hne hprime lo L hL
  exact ⟨B, hB, fun mass => reconstruct_exact _ B hB mass⟩

end NearCubicGates.Reconstruction

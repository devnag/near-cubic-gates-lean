import Proof.Gates.TwoScoreWindow
import Proof.Gates.ScalarReconstruction

/-! Injectivity and accepted inverse existence for the actual same-prime
    pair residue matrix, on arbitrary translated integer square frames. -/

set_option autoImplicit false

namespace NearCubicGates.Reconstruction

open scoped BigOperators Matrix
open TwoScoreProjections ProjectionBinomials ScalarWindow TomographyDirections

def pairMatrix (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (L : ℕ) :
    Matrix (PairResidueRow (fun p : primes => p.val)) (Fin L × Fin L) ℚ :=
  pairResidueMatrix (fun i : Fin L × Fin L => lo₁ + (i.1.val : ℤ))
    (fun i => lo₂ + (i.2.val : ℤ)) (fun p : primes => p.val)

theorem translated_mod_eq (p : ℕ) (hp : 0 < p) (lo x : ℤ) (r : Fin p) :
    (lo + x) % (p : ℤ) =
      ((residueIndex p hp (lo + (r.val : ℤ))).val : ℤ) ↔
      x % (p : ℤ) = (r.val : ℤ) := by
  rw [residueIndex_cast]
  have hr : (r.val : ℤ) % (p : ℤ) = r.val := Int.emod_eq_of_lt (by omega)
    (by exact_mod_cast r.isLt)
  constructor
  · intro h
    have hc := Int.ModEq.add_left_cancel' lo h
    simpa only [Int.ModEq, hr] using hc
  · intro h
    have hc : Int.ModEq (p : ℤ) x (r.val : ℤ) := by simpa only [Int.ModEq, hr] using h
    exact hc.add_left lo

theorem pairMatrix_translated_row (primes : Finset ℕ) (lo₁ lo₂ : ℤ) (L : ℕ)
    (mass : Fin L × Fin L → ℚ) (p : primes) (hp : 0 < p.val) (r : Fin p.val × Fin p.val) :
    (pairMatrix primes lo₁ lo₂ L *ᵥ mass)
      ⟨p, (residueIndex p.val hp (lo₁ + (r.1.val : ℤ)),
        residueIndex p.val hp (lo₂ + (r.2.val : ℤ)))⟩ =
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p.val hp r := by
  rcases r with ⟨r, s⟩
  rw [jointData_eq]
  simp only [pairMatrix, pairResidueMatrix, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [translated_mod_eq]

theorem pairMatrix_injective (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L)
    (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1))) :
    Function.Injective (fun mass : Fin L × Fin L → ℚ => pairMatrix primes lo₁ lo₂ L *ᵥ mass) := by
  intro a b hab
  have hzero : ∀ i, a i - b i = 0 := by
    apply square_window_zero primes hne hprime L hL (fun i => a i - b i) hsize
    intro p hp r
    let row : PairResidueRow (fun p : primes => p.val) :=
      ⟨⟨p, hp⟩, (residueIndex p (hprime p hp).pos (lo₁ + (r.1.val : ℤ)),
        residueIndex p (hprime p hp).pos (lo₂ + (r.2.val : ℤ)))⟩
    have hrow := congrFun hab row
    dsimp only [row] at hrow
    rw [pairMatrix_translated_row primes lo₁ lo₂ L a ⟨p, hp⟩ (hprime p hp).pos r,
      pairMatrix_translated_row primes lo₁ lo₂ L b ⟨p, hp⟩ (hprime p hp).pos r] at hrow
    rw [jointData, FiniteDistributions.pushforward_sub]
    exact sub_eq_zero.mpr hrow
  funext i
  exact sub_eq_zero.mp (hzero i)

theorem pair_inverse_exists (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L)
    (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1))) :
    ∃ B : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (pairMatrix primes lo₁ lo₂ L) B = true := by
  classical
  exact exists_checked_left_inverse (pairMatrix primes lo₁ lo₂ L)
    (pairMatrix_injective primes hne hprime lo₁ lo₂ L hL hsize)

theorem pair_reconstruction_complete (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (lo₁ lo₂ : ℤ) (L : ℕ) (hL : 2 ≤ L)
    (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1))) :
    ∃ B : Matrix (Fin L × Fin L) (PairResidueRow (fun p : primes => p.val)) ℚ,
      leftInverseCheck (pairMatrix primes lo₁ lo₂ L) B = true ∧
      ∀ mass : Fin L × Fin L → ℚ, B *ᵥ (pairMatrix primes lo₁ lo₂ L *ᵥ mass) = mass := by
  obtain ⟨B, hB⟩ := pair_inverse_exists primes hne hprime lo₁ lo₂ L hL hsize
  exact ⟨B, hB, fun mass => reconstruct_exact _ B hB mass⟩

end NearCubicGates.Reconstruction

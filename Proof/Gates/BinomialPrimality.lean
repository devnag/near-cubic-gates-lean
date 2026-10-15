import Proof.Gates.LaurentProjection
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Prime.Defs

/-! Kernel equals the principal binomial ideal, and hence these actual
    primitive binomials are prime. The proof uses finite polynomial fibers;
    primality is not assumed as an input. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped BigOperators LaurentPolynomial
open Polynomial

theorem positive_kernel_iff_dvd (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β) (f : Bivariate) :
    projection α β f = 0 ↔ positiveBinomial α β ∣ f := by
  constructor
  · intro h
    let L := boxSize f
    let mass : Fin L × Fin L → ℚ := fun i => (f.coeff i.1.val).coeff i.2.val
    have hgen : generating L mass = f := generating_coefficients f
    have hz : projection α β (generating L mass) = 0 := by rw [hgen]; exact h
    have hd := positive_projection_factor L (boxSize_positive f) mass α β hα hβ hc
      ((projection_generating_zero_iff L mass α β).mp hz)
    rwa [hgen] at hd
  · rintro ⟨g, rfl⟩
    simp

theorem negative_kernel_iff_dvd (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β) (f : Bivariate) :
    projection α (-(β : ℤ)) f = 0 ↔ negativeBinomial α β ∣ f := by
  constructor
  · intro h
    let L := boxSize f
    let mass : Fin L × Fin L → ℚ := fun i => (f.coeff i.1.val).coeff i.2.val
    have hgen : generating L mass = f := generating_coefficients f
    have hz : projection α (-(β : ℤ)) (generating L mass) = 0 := by rw [hgen]; exact h
    have hf := (projection_generating_zero_iff L mass α (-(β : ℤ))).mp hz
    have hd := negative_projection_factor L (boxSize_positive f) mass α β hα hβ hc
      (by simpa only [neg_mul, ← sub_eq_add_neg] using hf)
    rwa [hgen] at hd
  · rintro ⟨g, rfl⟩
    simp

theorem positiveBinomial_natDegree (α β : ℕ) : (positiveBinomial α β).natDegree = β := by
  simp only [positiveBinomial, U, V, ← Polynomial.C_pow]
  exact Polynomial.natDegree_X_pow_sub_C

theorem negativeBinomial_natDegree (α β : ℕ) : (negativeBinomial α β).natDegree = β := by
  rw [negativeBinomial, show (1 : Bivariate) = Polynomial.C 1 by simp,
    Polynomial.natDegree_sub_C]
  rw [U, V, ← Polynomial.C_pow, mul_comm]
  rw [Polynomial.natDegree_C_mul (pow_ne_zero α Polynomial.X_ne_zero), Polynomial.natDegree_X_pow]

theorem positiveBinomial_prime (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β) : Prime (positiveBinomial α β) := by
  have hd : 0 < (positiveBinomial α β).natDegree := by rw [positiveBinomial_natDegree]; exact hβ
  refine ⟨?_, Polynomial.not_isUnit_of_natDegree_pos _ hd, ?_⟩
  · intro h
    simp [h] at hd
  · intro f g hfg
    have hzero := (positive_kernel_iff_dvd α β hα hβ hc (f * g)).mpr hfg
    rw [map_mul] at hzero
    rcases mul_eq_zero.mp hzero with hf | hg
    · exact Or.inl ((positive_kernel_iff_dvd α β hα hβ hc f).mp hf)
    · exact Or.inr ((positive_kernel_iff_dvd α β hα hβ hc g).mp hg)

theorem negativeBinomial_prime (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β) : Prime (negativeBinomial α β) := by
  have hd : 0 < (negativeBinomial α β).natDegree := by rw [negativeBinomial_natDegree]; exact hβ
  refine ⟨?_, Polynomial.not_isUnit_of_natDegree_pos _ hd, ?_⟩
  · intro h
    simp [h] at hd
  · intro f g hfg
    have hzero := (negative_kernel_iff_dvd α β hα hβ hc (f * g)).mpr hfg
    rw [map_mul] at hzero
    rcases mul_eq_zero.mp hzero with hf | hg
    · exact Or.inl ((negative_kernel_iff_dvd α β hα hβ hc f).mp hf)
    · exact Or.inr ((negative_kernel_iff_dvd α β hα hβ hc g).mp hg)

end
end NearCubicGates.ProjectionBinomials

import Proof.Gates.BinomialPrimality
import Mathlib.Algebra.Polynomial.RingDivision

/-! Explicit nonassociation tests by substitution. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped LaurentPolynomial
open Polynomial

theorem T_sub_T_ne_zero (n m : ℤ) (h : n ≠ m) :
    (LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial ℚ) ≠ 0 := by
  intro hz
  have he : (LaurentPolynomial.T n : LaurentPolynomial ℚ) = LaurentPolynomial.T m := sub_eq_zero.mp hz
  have hc := congrArg (fun f : LaurentPolynomial ℚ => f.coeff n) he
  have hn := laurent_term_coeff 1 n n
  have hm := laurent_term_coeff 1 m n
  simp only [map_one, one_mul] at hn
  simp only [map_one, one_mul, if_neg (Ne.symm h)] at hm
  rw [hn, hm] at hc
  norm_num at hc

theorem positive_projection_other (α β : ℤ) (a b : ℕ) :
    projection α β (positiveBinomial a b) =
      LaurentPolynomial.T ((b : ℤ) * α) - LaurentPolynomial.T ((a : ℤ) * β) := by
  simp [positiveBinomial, LaurentPolynomial.T_pow]

theorem negative_projection_other (α β : ℤ) (a b : ℕ) :
    projection α β (negativeBinomial a b) =
      LaurentPolynomial.T ((b : ℤ) * α + (a : ℤ) * β) - LaurentPolynomial.T 0 := by
  simp only [negativeBinomial, map_sub, map_mul, map_pow, map_one, projection_U,
    projection_V, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add, LaurentPolynomial.T_zero]

theorem positive_not_dvd_positive (α β a b : ℕ)
    (hdet : (b : ℤ) * α ≠ (a : ℤ) * β) :
    ¬ positiveBinomial α β ∣ positiveBinomial a b := by
  rintro ⟨g, hg⟩
  have hz : projection α β (positiveBinomial a b) = 0 := by rw [hg]; simp
  rw [positive_projection_other] at hz
  exact T_sub_T_ne_zero _ _ hdet hz

theorem negative_not_dvd_negative (α β a b : ℕ)
    (hdet : (b : ℤ) * α ≠ (a : ℤ) * β) :
    ¬ negativeBinomial α β ∣ negativeBinomial a b := by
  rintro ⟨g, hg⟩
  have hz : projection α (-(β : ℤ)) (negativeBinomial a b) = 0 := by rw [hg]; simp
  rw [negative_projection_other] at hz
  exact T_sub_T_ne_zero _ _ (by intro he; apply hdet; nlinarith) hz

theorem positive_not_dvd_negative (α β a b : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b) :
    ¬ positiveBinomial α β ∣ negativeBinomial a b := by
  rintro ⟨g, hg⟩
  have hz : projection α β (negativeBinomial a b) = 0 := by rw [hg]; simp
  rw [negative_projection_other] at hz
  exact T_sub_T_ne_zero _ _ (by positivity) hz

theorem negative_not_dvd_positive (α β a b : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b) :
    ¬ negativeBinomial α β ∣ positiveBinomial a b := by
  rintro ⟨g, hg⟩
  have hz : projection α (-(β : ℤ)) (positiveBinomial a b) = 0 := by rw [hg]; simp
  simp only [positiveBinomial, map_sub, map_pow, projection_U, projection_V,
    LaurentPolynomial.T_pow] at hz
  exact T_sub_T_ne_zero _ _ (by
    have h1 : (0 : ℤ) < (b : ℤ) * α := by positivity
    have h2 : (a : ℤ) * -(β : ℤ) < 0 := by
      have : (0 : ℤ) < (a : ℤ) * β := by positivity
      nlinarith
    omega) hz

def verticalBinomial : Bivariate := U - 1

theorem verticalBinomial_prime : Prime verticalBinomial := by
  simpa [verticalBinomial, U] using Polynomial.prime_X_sub_C (1 : Polynomial ℚ)

theorem verticalBinomial_natDegree : verticalBinomial.natDegree = 1 := by
  change (Polynomial.X - Polynomial.C (1 : Polynomial ℚ)).natDegree = 1
  rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X]

theorem binomials_not_dvd_vertical (α β : ℕ) (hα : 0 < α) :
    (¬ positiveBinomial α β ∣ verticalBinomial) ∧
      (¬ negativeBinomial α β ∣ verticalBinomial) := by
  constructor
  · rintro ⟨g, hg⟩
    have hz : projection α β verticalBinomial = 0 := by rw [hg]; simp
    simp only [verticalBinomial, map_sub, map_one, projection_U] at hz
    rw [← LaurentPolynomial.T_zero] at hz
    exact T_sub_T_ne_zero _ _ (by exact_mod_cast Nat.ne_of_gt hα) hz
  · rintro ⟨g, hg⟩
    have hz : projection α (-(β : ℤ)) verticalBinomial = 0 := by rw [hg]; simp
    simp only [verticalBinomial, map_sub, map_one, projection_U] at hz
    rw [← LaurentPolynomial.T_zero] at hz
    exact T_sub_T_ne_zero _ _ (by exact_mod_cast Nat.ne_of_gt hα) hz

theorem vertical_not_dvd_binomials (α β : ℕ) (hα : 0 < α) :
    (¬ verticalBinomial ∣ positiveBinomial α β) ∧
      (¬ verticalBinomial ∣ negativeBinomial α β) := by
  have hv : projection 0 1 verticalBinomial = 0 := by simp [verticalBinomial]
  constructor
  · rintro ⟨g, hg⟩
    have hz : projection 0 1 (positiveBinomial α β) = 0 := by rw [hg, map_mul, hv, zero_mul]
    rw [positive_projection_other] at hz
    simp only [mul_zero, mul_one] at hz
    exact T_sub_T_ne_zero _ _ (by exact_mod_cast Nat.ne_of_gt hα |>.symm) hz
  · rintro ⟨g, hg⟩
    have hz : projection 0 1 (negativeBinomial α β) = 0 := by rw [hg, map_mul, hv, zero_mul]
    rw [negative_projection_other] at hz
    simp only [mul_zero, mul_one, zero_add] at hz
    exact T_sub_T_ne_zero _ _ (by exact_mod_cast Nat.ne_of_gt hα) hz

end
end NearCubicGates.ProjectionBinomials

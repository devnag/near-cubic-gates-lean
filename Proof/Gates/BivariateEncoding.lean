import Proof.Gates.ProjectionBinomials

/-! Exact coefficients of the actual two-score generating polynomial. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped BigOperators
open Polynomial

theorem generating_term (c : ℚ) (a b : ℕ) :
    rationalConstant c * monomial a b =
      Polynomial.monomial a (Polynomial.monomial b c) := by
  simp only [rationalConstant, RingHom.comp_apply, monomial, U, V,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow]
  ring

theorem generating_coeff (L : ℕ) (mass : Fin L × Fin L → ℚ)
    (a b : Fin L) : ((generating L mass).coeff a.val).coeff b.val = mass (a, b) := by
  classical
  simp only [generating, generating_term, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single (a, b)]
  · simp
  · intro i _ hne
    by_cases ha : a.val = i.1.val
    · have ha' : a = i.1 := Fin.ext ha
      have hb : b.val ≠ i.2.val := by
        intro hb
        exact hne (Prod.ext ha'.symm (Fin.ext hb).symm)
      simp [Polynomial.coeff_monomial, ha, Ne.symm hb]
    · simp [Ne.symm ha]
  · simp

theorem generating_injective (L : ℕ) : Function.Injective (generating L) := by
  intro mass other h
  funext i
  have hc := congrArg (fun f : Bivariate => (f.coeff i.1.val).coeff i.2.val) h
  simpa only [generating_coeff] using hc

theorem generating_zero_iff (L : ℕ) (mass : Fin L × Fin L → ℚ) :
    generating L mass = 0 ↔ ∀ i, mass i = 0 := by
  constructor
  · intro h i
    have hc := congrArg (fun f : Bivariate => (f.coeff i.1.val).coeff i.2.val) h
    simpa only [generating_coeff, Polynomial.coeff_zero] using hc
  · intro h
    simp [generating, h]

theorem generating_coeff_outside (L : ℕ) (mass : Fin L × Fin L → ℚ)
    (a b : ℕ) (hout : L ≤ a ∨ L ≤ b) :
    ((generating L mass).coeff a).coeff b = 0 := by
  classical
  simp only [generating, generating_term, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rcases hout with ha | hb
  · have hi : i.1.val ≠ a := by have := i.1.isLt; omega
    simp [Polynomial.coeff_monomial, hi]
  · have hi : i.2.val ≠ b := by have := i.2.isLt; omega
    rw [Polynomial.coeff_monomial]
    split <;> simp [Polynomial.coeff_monomial, hi]

def boxSize (f : Bivariate) : ℕ :=
  f.natDegree + 2 + f.support.sup (fun a => (f.coeff a).natDegree)

theorem boxSize_positive (f : Bivariate) : 1 ≤ boxSize f := by unfold boxSize; omega

theorem boxSize_outer (f : Bivariate) : f.natDegree < boxSize f := by unfold boxSize; omega

theorem boxSize_inner (f : Bivariate) (a : ℕ) : (f.coeff a).natDegree < boxSize f := by
  classical
  by_cases ha : a ∈ f.support
  · have h := Finset.le_sup (f := fun a => (f.coeff a).natDegree) ha
    unfold boxSize
    omega
  · have hz : f.coeff a = 0 := Polynomial.notMem_support_iff.mp ha
    simp only [hz, Polynomial.natDegree_zero]
    have := boxSize_positive f
    omega

/-- Every rational bivariate polynomial has an actual finite square encoding.
    The bound is used for algebra, with no algorithmic speedup claimed. -/
theorem generating_coefficients (f : Bivariate) :
    generating (boxSize f) (fun i => (f.coeff i.1.val).coeff i.2.val) = f := by
  ext a b
  by_cases ha : a < boxSize f
  · by_cases hb : b < boxSize f
    · exact generating_coeff (boxSize f) _ ⟨a, ha⟩ ⟨b, hb⟩
    · rw [generating_coeff_outside _ _ a b (Or.inr (by omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((boxSize_inner f a).trans_le (by omega))]
  · rw [generating_coeff_outside _ _ a b (Or.inl (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((boxSize_outer f).trans_le (by omega)),
      Polynomial.coeff_zero]

end
end NearCubicGates.ProjectionBinomials

import Proof.Gates.BivariateEncoding
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! Literal polynomial substitution into the Laurent ring and extraction of
    every projected fiber coefficient. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped BigOperators LaurentPolynomial
open Polynomial

def projection (α β : ℤ) : Bivariate →+* LaurentPolynomial ℚ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T β))
    (LaurentPolynomial.T α)

@[simp] theorem projection_U (α β : ℤ) : projection α β U = LaurentPolynomial.T α := by
  simp [projection, U]

@[simp] theorem projection_V (α β : ℤ) : projection α β V = LaurentPolynomial.T β := by
  simp [projection, V]

@[simp] theorem projection_constant (α β : ℤ) (c : ℚ) :
    projection α β (rationalConstant c) = LaurentPolynomial.C c := by
  simp [projection, rationalConstant]

theorem projection_term (α β : ℤ) (c : ℚ) (a b : ℕ) :
    projection α β (rationalConstant c * monomial a b) =
      LaurentPolynomial.C c * LaurentPolynomial.T (α * a + β * b) := by
  simp only [map_mul, monomial, map_pow, projection_U, projection_V, projection_constant,
    LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
  congr 2; ring

theorem laurent_term_coeff (c : ℚ) (n k : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n).coeff k = if n = k then c else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [AddMonoidAlgebra.coeff_single]
  exact Finsupp.single_apply

theorem projection_generating_coeff (L : ℕ) (mass : Fin L × Fin L → ℚ)
    (α β c : ℤ) :
    (projection α β (generating L mass)).coeff c =
      ∑ i, if α * (i.1.val : ℤ) + β * (i.2.val : ℤ) = c then mass i else 0 := by
  simp only [generating, map_sum, projection_term, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, laurent_term_coeff]

theorem projection_generating_zero_iff (L : ℕ) (mass : Fin L × Fin L → ℚ) (α β : ℤ) :
    projection α β (generating L mass) = 0 ↔ ∀ c : ℤ,
      (∑ i, if α * (i.1.val : ℤ) + β * (i.2.val : ℤ) = c then mass i else 0) = 0 := by
  constructor
  · intro h c
    rw [← projection_generating_coeff, h]
    rfl
  · intro h
    apply LaurentPolynomial.ext
    intro c
    rw [projection_generating_coeff, h c]
    rfl

@[simp] theorem projection_positiveBinomial (α β : ℕ) :
    projection α β (positiveBinomial α β) = 0 := by
  simp [positiveBinomial, LaurentPolynomial.T_pow, mul_comm]

@[simp] theorem projection_negativeBinomial (α β : ℕ) :
    projection α (-(β : ℤ)) (negativeBinomial α β) = 0 := by
  simp only [negativeBinomial, map_sub, map_mul, map_pow, map_one, projection_U,
    projection_V, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
  have he : (β : ℤ) * α + (α : ℤ) * -(β : ℤ) = 0 := by ring
  rw [he, LaurentPolynomial.T_zero, sub_self]

end
end NearCubicGates.ProjectionBinomials

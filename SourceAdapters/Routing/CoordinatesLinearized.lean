import SourceAdapters.Routing.CoordinatesArray
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compact coefficient arrays for the coordinate construction

The coordinate construction in `app:affine-embedding` represents each coordinate as a sum of mH
Frobenius monomials. The triangular construction preserves this representation structurally. The arrays below use
only addition, multiplication, inversion, finite evaluation, padding and
squaring followed by a one-position shift. They never enumerate the
exponentially many dense coefficient positions.

These are actual polynomial identities, including the zero-dimensional
base cases. This module makes no paid machine-generation claim.-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial

variable {F : Type*} [Field F]

/-- The compact array denotes only monomials with power-of-two exponents. -/
def linearizedPolynomial {k : ℕ} (c : Fin k → F) : F[X] :=
  ∑ r, C (c r) * X ^ (2 ^ r.val)

/-- Evaluation directly from the compact array. -/
def linearizedValue {k : ℕ} (c : Fin k → F) (x : F) : F :=
  ∑ r, c r * x ^ (2 ^ r.val)

def coefficientAdd {k : ℕ} (a b : Fin k → F) : Fin k → F := fun r => a r + b r

def coefficientScale {k : ℕ} (a : F) (c : Fin k → F) : Fin k → F := fun r => a * c r

/-- Append one zero coefficient at the largest exponent. -/
def coefficientPad {k : ℕ} (c : Fin k → F) : Fin (k+1) → F :=
  Fin.lastCases 0 c

/-- Squaring moves every Frobenius monomial to the next position. -/
def coefficientSquareShift {k : ℕ} (c : Fin k → F) : Fin (k+1) → F :=
  Fin.cases 0 (fun r => (c r)^2)

theorem linearizedPolynomial_eval {k : ℕ} (c : Fin k → F) (x : F) :
    (linearizedPolynomial c).eval x = linearizedValue c x := by
  simp [linearizedPolynomial, linearizedValue, eval_finsetSum]

theorem linearizedPolynomial_add {k : ℕ} (a b : Fin k → F) :
    linearizedPolynomial (coefficientAdd a b) = linearizedPolynomial a + linearizedPolynomial b := by
  simp [linearizedPolynomial, coefficientAdd, add_mul, Finset.sum_add_distrib]

theorem linearizedPolynomial_scale {k : ℕ} (a : F) (c : Fin k → F) :
    linearizedPolynomial (coefficientScale a c) = C a * linearizedPolynomial c := by
  simp [linearizedPolynomial, coefficientScale, Finset.mul_sum, mul_assoc]

theorem linearizedPolynomial_pad {k : ℕ} (c : Fin k → F) :
    linearizedPolynomial (coefficientPad c) = linearizedPolynomial c := by
  simp [linearizedPolynomial, Fin.sum_univ_castSucc, coefficientPad]

theorem linearizedPolynomial_squareShift [CharP F 2] {k : ℕ} (c : Fin k → F) :
    linearizedPolynomial (coefficientSquareShift c) = (linearizedPolynomial c)^2 := by
  simp only [linearizedPolynomial, Fin.sum_univ_succ, coefficientSquareShift,
    Fin.cases_zero, Fin.cases_succ, map_zero, zero_mul, zero_add, Fin.val_succ]
  rw [CharTwo.sum_sq]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_pow, ← map_pow, ← pow_mul, Nat.pow_succ]

/-- Coefficients of the normalized new coordinate. -/
def unitCoefficients {k : ℕ} (c : Fin k → F) (x : F) : Fin k → F :=
  coefficientScale (linearizedValue c x)⁻¹ c

theorem linearizedPolynomial_unit {k : ℕ} (c : Fin k → F) (x : F) :
    linearizedPolynomial (unitCoefficients c x) = unitStep (linearizedPolynomial c) x := by
  rw [unitCoefficients, linearizedPolynomial_scale, unitStep, linearizedPolynomial_eval]

/-- The actual compact annihilator array has exactly n+1 positions. -/
def annihilatorCoefficients (e : ℕ → F) : (n : ℕ) → Fin (n+1) → F
  | 0 => fun _ => 1
  | n+1 => coefficientAdd (coefficientSquareShift (annihilatorCoefficients e n))
      (coefficientScale (linearizedValue (annihilatorCoefficients e n) (e n))
        (coefficientPad (annihilatorCoefficients e n)))

theorem annihilatorCoefficients_correct [CharP F 2] (e : ℕ → F) (n : ℕ) :
    linearizedPolynomial (annihilatorCoefficients e n) = annihilator e n := by
  induction n with
  | zero => simp [annihilatorCoefficients, linearizedPolynomial, annihilator]
  | succ n ih =>
    rw [annihilatorCoefficients, linearizedPolynomial_add, linearizedPolynomial_squareShift,
      linearizedPolynomial_scale, linearizedPolynomial_pad, ← linearizedPolynomial_eval, ih]
    rfl

/-- Only the first n rows are retained by the solver; each row has n positions. -/
def coordinateCoefficients (e : ℕ → F) : (n : ℕ) → ℕ → Fin n → F
  | 0, _ => Fin.elim0
  | n+1, j =>
      if j = n then unitCoefficients (annihilatorCoefficients e n) (e n)
      else coefficientAdd (coefficientPad (coordinateCoefficients e n j))
        (coefficientScale (linearizedValue (coordinateCoefficients e n j) (e n))
          (unitCoefficients (annihilatorCoefficients e n) (e n)))

theorem coordinateCoefficients_correct [CharP F 2] (e : ℕ → F) (n j : ℕ) :
    linearizedPolynomial (coordinateCoefficients e n j) = coordinates e n j := by
  induction n generalizing j with
  | zero => simp [coordinateCoefficients, linearizedPolynomial, coordinates]
  | succ n ih =>
    by_cases hj : j = n
    · rw [coordinateCoefficients, if_pos hj, coordinates, if_pos hj,
        linearizedPolynomial_unit, annihilatorCoefficients_correct]
    · rw [coordinateCoefficients, if_neg hj, coordinates, if_neg hj,
        linearizedPolynomial_add, linearizedPolynomial_pad, linearizedPolynomial_scale,
        linearizedPolynomial_unit, annihilatorCoefficients_correct,
        ← linearizedPolynomial_eval, ih]
      rfl

/-- Structural representation, rather than equality of polynomial functions. -/
theorem annihilator_linearized [CharP F 2] (e : ℕ → F) (n : ℕ) :
    annihilator e n = ∑ r : Fin (n+1), C (annihilatorCoefficients e n r) * X ^ (2 ^ r.val) :=
  (annihilatorCoefficients_correct e n).symm

theorem coordinates_linearized [CharP F 2] (e : ℕ → F) (n j : ℕ) :
    coordinates e n j = ∑ r : Fin n, C (coordinateCoefficients e n j r) * X ^ (2 ^ r.val) :=
  (coordinateCoefficients_correct e n j).symm

end NearCubicGates.Adapters.Routing.Coordinates

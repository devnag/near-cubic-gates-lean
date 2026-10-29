import SourceAdapters.Routing.CoordinatesKernel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Degree bounds for the triangular coordinate construction

The degree estimate in `lem:acsp-degree` uses coordinate degree at most 2^(mH-1).
The triangular construction computes these coordinate polynomials. These are bounds for the actual
polynomials of CoordinatesStep/Kernel, over any field and any candidate
basis sequence. In particular, no independence, characteristic-two or
successful-pivot premise is needed for the degree statements.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing.Coordinates

open Polynomial

variable {F : Type*} [Field F]

/-- Normalization never increases degree, including at a zero pivot. -/
theorem unitStep_degree_le (p : F[X]) (e : F) :
    (unitStep p e).degree ≤ p.degree := by
  by_cases hc : p.eval e = 0
  · simp [unitStep, hc]
  · exact le_of_eq (degree_C_mul (inv_ne_zero hc))

theorem unitStep_natDegree_le (p : F[X]) (e : F) :
    (unitStep p e).natDegree ≤ p.natDegree :=
  natDegree_C_mul_le _ _

/-- Updating one coordinate retains the larger of the two old degree bounds. -/
theorem coordinateStep_natDegree_le (p l : F[X]) (e : F) :
    (coordinateStep p l e).natDegree ≤ max l.natDegree p.natDegree := by
  apply natDegree_add_le_of_degree_le (le_max_left _ _)
  exact ((natDegree_C_mul_le _ _).trans (unitStep_natDegree_le p e)).trans (le_max_right _ _)

/-- A doubled annihilator has at most twice the prior degree. -/
theorem annihilatorStep_natDegree_le (p : F[X]) (e : F) :
    (annihilatorStep p e).natDegree ≤ 2 * p.natDegree := by
  apply natDegree_add_le_of_degree_le natDegree_pow_le
  exact (natDegree_C_mul_le _ _).trans (by omega)

/-- The leading monomial cannot cancel against the lower-degree correction. -/
theorem annihilatorStep_isMonicOfDegree (p : F[X]) (e : F) (n : ℕ)
    (hn : 0 < n) (hp : IsMonicOfDegree p n) :
    IsMonicOfDegree (annihilatorStep p e) (2 * n) := by
  have hc : (C (p.eval e) * p).natDegree < n * 2 :=
    (natDegree_C_mul_le _ _).trans_lt (by rw [hp.natDegree_eq]; omega)
  simpa only [annihilatorStep, Nat.mul_comm] using (hp.pow 2).add_right hc

/-- Every recursive annihilator is monic of exactly the expected degree. -/
theorem annihilator_isMonicOfDegree (e : ℕ → F) (n : ℕ) :
    IsMonicOfDegree (annihilator e n) (2 ^ n) := by
  induction n with
  | zero => simpa only [annihilator, pow_zero] using isMonicOfDegree_X F
  | succ n ih =>
    simpa only [annihilator, pow_succ, Nat.mul_comm] using
      annihilatorStep_isMonicOfDegree (annihilator e n) (e n) (2 ^ n) (by positivity) ih

theorem annihilator_natDegree (e : ℕ → F) (n : ℕ) :
    (annihilator e n).natDegree = 2 ^ n :=
  (annihilator_isMonicOfDegree e n).natDegree_eq

theorem annihilator_natDegree_le (e : ℕ → F) (n : ℕ) :
    (annihilator e n).natDegree ≤ 2 ^ n :=
  le_of_eq (annihilator_natDegree e n)

theorem annihilator_monic (e : ℕ → F) (n : ℕ) :
    (annihilator e n).Monic :=
  (annihilator_isMonicOfDegree e n).monic

end NearCubicGates.Adapters.Routing.Coordinates

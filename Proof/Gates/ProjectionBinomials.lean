import Proof.Gates.ProjectionFibers
import Proof.Gates.FiberDivisibility
import Proof.Gates.TwoScoreProjections
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Actual bivariate generating polynomials and their primitive-direction
    factors. Zero residue data supply the fiber-zero premise through the
    already proved scalar window. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped BigOperators
open Polynomial
open TwoScoreProjections ScalarWindow

abbrev Bivariate := Polynomial (Polynomial ℚ)

def U : Bivariate := X
def V : Bivariate := C X
def rationalConstant : ℚ →+* Bivariate := Polynomial.C.comp Polynomial.C

def monomial (a b : ℕ) : Bivariate := U ^ a * V ^ b

noncomputable def generating (L : ℕ) (mass : Fin L × Fin L → ℚ) : Bivariate :=
  ∑ i, rationalConstant (mass i) * monomial i.1.val i.2.val

def positiveBinomial (α β : ℕ) : Bivariate := U ^ β - V ^ α
def negativeBinomial (α β : ℕ) : Bivariate := U ^ β * V ^ α - 1

theorem short_projection_zero_all (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (L : ℕ) (hL : 1 ≤ L) (mass : Fin L × Fin L → ℚ) (α β : ℤ)
    (hnorm : α.natAbs + β.natAbs ≤ (window primes - 1) / (L - 1))
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p (hprime p hp).pos r = 0) :
    ∀ c : ℤ, (∑ i : Fin L × Fin L,
      if α * (i.1.val : ℤ) + β * (i.2.val : ℤ) = c then mass i else 0) = 0 := by
  intro c
  let lo := boxProjectionLo L α β
  let W := boxProjectionWidth L α β
  by_cases hc : lo ≤ c ∧ c < lo + (W : ℤ)
  · let j : Fin W := ⟨(c - lo).toNat, by omega⟩
    have hj : lo + (j.val : ℤ) = c := by
      dsimp [j]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hz := box_short_projection_zero primes hne hprime L hL mass α β hnorm hdata j
    simpa only [← hj] using hz
  · apply Finset.sum_eq_zero
    intro i _
    have hi := box_projection_bounds L hL α β i.1 i.2
    have hn : α * (i.1.val : ℤ) + β * (i.2.val : ℤ) ≠ c := by
      intro he
      exact hc (he ▸ hi)
    simp only [hn, ↓reduceIte]

theorem positive_projection_factor (L : ℕ) (hL : 1 ≤ L)
    (mass : Fin L × Fin L → ℚ) (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β)
    (hzero : ∀ c : ℤ, (∑ i : Fin L × Fin L,
      if (α : ℤ) * i.1.val + (β : ℤ) * i.2.val = c then mass i else 0) = 0) :
    positiveBinomial α β ∣ generating L mass := by
  classical
  letI : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  apply FiberDivisibility.factor_of_zero_fibers
    (fun i : Fin L × Fin L => (α : ℤ) * i.1.val + (β : ℤ) * i.2.val)
    (fun i => rationalConstant (mass i)) (fun i => monomial i.1.val i.2.val)
  · intro c
    have h := congrArg rationalConstant (hzero c)
    simpa only [map_sum, apply_ite, map_zero] using h
  · intro i j hij
    apply ProjectionFibers.positive_monomial_factor U V α β hα hβ hc
    exact_mod_cast hij

theorem negative_projection_factor (L : ℕ) (hL : 1 ≤ L)
    (mass : Fin L × Fin L → ℚ) (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β)
    (hzero : ∀ c : ℤ, (∑ i : Fin L × Fin L,
      if (α : ℤ) * i.1.val - (β : ℤ) * i.2.val = c then mass i else 0) = 0) :
    negativeBinomial α β ∣ generating L mass := by
  classical
  letI : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  apply FiberDivisibility.factor_of_zero_fibers
    (fun i : Fin L × Fin L => (α : ℤ) * i.1.val - (β : ℤ) * i.2.val)
    (fun i => rationalConstant (mass i)) (fun i => monomial i.1.val i.2.val)
  · intro c
    have h := congrArg rationalConstant (hzero c)
    simpa only [map_sum, apply_ite, map_zero] using h
  · intro i j hij
    apply ProjectionFibers.negative_monomial_factor U V α β hα hβ hc
    have hh : (α : ℤ) * i.1.val + (β : ℤ) * j.2.val =
        (α : ℤ) * j.1.val + (β : ℤ) * i.2.val := by omega
    exact_mod_cast hh

/-- Positive primitive directions with the exact shortness bound of the proof of `lem:two-window`. -/
theorem positive_factor_of_joint_data (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (L : ℕ) (hL : 1 ≤ L) (mass : Fin L × Fin L → ℚ)
    (α β : ℕ) (hα : 0 < α) (hβ : 0 < β) (hc : α.Coprime β)
    (hnorm : α + β ≤ (window primes - 1) / (L - 1))
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p (hprime p hp).pos r = 0) :
    positiveBinomial α β ∣ generating L mass := by
  apply positive_projection_factor L hL mass α β hα hβ hc
  exact short_projection_zero_all primes hne hprime L hL mass α β
    (by simpa using hnorm) hdata

/-- Negative primitive directions, without clearing Laurent denominators. -/
theorem negative_factor_of_joint_data (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (L : ℕ) (hL : 1 ≤ L) (mass : Fin L × Fin L → ℚ)
    (α β : ℕ) (hα : 0 < α) (hβ : 0 < β) (hc : α.Coprime β)
    (hnorm : α + β ≤ (window primes - 1) / (L - 1))
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p (hprime p hp).pos r = 0) :
    negativeBinomial α β ∣ generating L mass := by
  apply negative_projection_factor L hL mass α β hα hβ hc
  have h := short_projection_zero_all primes hne hprime L hL mass α (- (β : ℤ))
    (by simpa using hnorm) hdata
  simpa only [neg_mul, ← sub_eq_add_neg] using h

end
end NearCubicGates.ProjectionBinomials

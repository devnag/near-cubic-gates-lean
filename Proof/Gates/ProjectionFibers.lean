import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! The primitive-direction kernel argument starts with its literal fibers.
    Equal projected exponents differ by an integer multiple of the kernel
    vector. The corresponding monomial differences have the manuscript's
    binomial factor, for both signs of the direction. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionFibers

theorem positive_fiber_steps (α β : ℕ) (_hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β) (a b c d : ℕ) (h : α * a + β * b = α * c + β * d) :
    (∃ t : ℕ, a = c + β * t ∧ d = b + α * t) ∨
      (∃ t : ℕ, c = a + β * t ∧ b = d + α * t) := by
  have forward (a b c d : ℕ) (heq : α * a + β * b = α * c + β * d)
      (hca : c ≤ a) : ∃ t : ℕ, a = c + β * t ∧ d = b + α * t := by
    have hαle := Nat.mul_le_mul_left α hca
    have hβle : β * b ≤ β * d := by omega
    have hdb : b ≤ d := Nat.le_of_mul_le_mul_left hβle hβ
    have haeq : a = c + (a - c) := by omega
    have hdeq : d = b + (d - b) := by omega
    have hdiff : α * (a - c) = β * (d - b) := by nlinarith [heq]
    have hdvd : β ∣ a - c := hc.symm.dvd_of_dvd_mul_left ⟨d - b, hdiff⟩
    obtain ⟨t, ht⟩ := hdvd
    have hother : d - b = α * t := by nlinarith
    exact ⟨t, by omega, by omega⟩
  rcases le_total c a with hca | hac
  · exact Or.inl (forward a b c d h hca)
  · exact Or.inr (forward c d a b h.symm hac)

section Rings

variable {R : Type*} [CommRing R]

theorem positive_monomial_factor (U V : R) (α β : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hc : α.Coprime β)
    (a b c d : ℕ) (h : α * a + β * b = α * c + β * d) :
    U ^ β - V ^ α ∣ U ^ a * V ^ b - U ^ c * V ^ d := by
  have forward (a b c d t : ℕ) (ha : a = c + β * t) (hd : d = b + α * t) :
      U ^ β - V ^ α ∣ U ^ a * V ^ b - U ^ c * V ^ d := by
    have hp := sub_dvd_pow_sub_pow (U ^ β) (V ^ α) t
    have heq : U ^ a * V ^ b - U ^ c * V ^ d =
        (U ^ c * V ^ b) * ((U ^ β) ^ t - (V ^ α) ^ t) := by
      rw [ha, hd, pow_add, pow_add, pow_mul, pow_mul]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_right hp _
  rcases positive_fiber_steps α β hα hβ hc a b c d h with ⟨t, ha, hd⟩ | ⟨t, hc', hb⟩
  · exact forward a b c d t ha hd
  · have hv := forward c d a b t hc' hb
    simpa only [neg_sub] using dvd_neg.mpr hv

theorem negative_monomial_factor (U V : R) (α β : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hc : α.Coprime β)
    (a b c d : ℕ) (h : α * a + β * d = α * c + β * b) :
    U ^ β * V ^ α - 1 ∣ U ^ a * V ^ b - U ^ c * V ^ d := by
  have forward (a b c d t : ℕ) (ha : a = c + β * t) (hb : b = d + α * t) :
      U ^ β * V ^ α - 1 ∣ U ^ a * V ^ b - U ^ c * V ^ d := by
    have hp := sub_one_dvd_pow_sub_one (U ^ β * V ^ α) t
    have heq : U ^ a * V ^ b - U ^ c * V ^ d =
        (U ^ c * V ^ d) * ((U ^ β * V ^ α) ^ t - 1) := by
      rw [ha, hb, pow_add, pow_add, mul_pow, pow_mul, pow_mul]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_right hp _
  rcases positive_fiber_steps α β hα hβ hc a d c b h with ⟨t, ha, hb⟩ | ⟨t, hc', hd⟩
  · exact forward a b c d t ha hb
  · have hv := forward c d a b t hc' hd
    simpa only [neg_sub] using dvd_neg.mpr hv

end Rings

end NearCubicGates.ProjectionFibers

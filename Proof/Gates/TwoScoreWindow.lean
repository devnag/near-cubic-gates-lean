import Proof.Gates.TomographyFactorFamily
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! The full finite square-box distribution theorem, using actual joint
    residue data and the manuscript's S(q) reconstruction criterion. -/

set_option autoImplicit false

namespace NearCubicGates.ProjectionBinomials

noncomputable section

open scoped BigOperators
open Polynomial TwoScoreProjections ScalarWindow TomographyDirections

theorem vertical_projection_factor (L : ℕ) (hL : 1 ≤ L)
    (mass : Fin L × Fin L → ℚ)
    (hzero : ∀ c : ℤ, (∑ i : Fin L × Fin L, if (i.2.val : ℤ) = c then mass i else 0) = 0) :
    verticalBinomial ∣ generating L mass := by
  classical
  letI : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  apply FiberDivisibility.factor_of_zero_fibers (fun i : Fin L × Fin L => (i.2.val : ℤ))
    (fun i => rationalConstant (mass i)) (fun i => monomial i.1.val i.2.val)
  · intro c
    have h := congrArg rationalConstant (hzero c)
    simpa only [map_sum, apply_ite, map_zero] using h
  · intro i j hij
    have he : i.2.val = j.2.val := by exact_mod_cast hij
    have hd := dvd_sub (sub_one_dvd_pow_sub_one U i.1.val)
      (sub_one_dvd_pow_sub_one U j.1.val)
    have hd' : U - 1 ∣ U ^ i.1.val - U ^ j.1.val := by
      convert hd using 1; ring
    have heq : monomial i.1.val i.2.val - monomial j.1.val j.2.val =
        (U ^ i.1.val - U ^ j.1.val) * V ^ i.2.val := by
      simp only [monomial, ← he]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_left hd' _

theorem generating_natDegree_bound (L : ℕ) (hL : 1 ≤ L) (mass : Fin L × Fin L → ℚ) :
    (generating L mass).natDegree ≤ L - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  ext b
  exact generating_coeff_outside L mass a b (Or.inl (by omega))

theorem all_factors_of_joint_data (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hwindow : q ≤ (window primes - 1) / (L - 1)) (mass : Fin L × Fin L → ℚ)
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p (hprime p hp).pos r = 0) :
    ∀ d : Direction q, factor q d ∣ generating L mass := by
  intro d
  rcases d with _ | ⟨i, flag⟩
  · apply vertical_projection_factor L hL mass
    have hz := short_projection_zero_all primes hne hprime L hL mass 0 1
      (by simpa using hq.trans hwindow) hdata
    simpa using hz
  · have hm := Finset.mem_Icc.mp i.1.property
    have ha := shell_bounds i.1.val hm.1 i.2.property
    have hc := PrimitiveDirectionSeparation.shell_coprime i.1.val i.2.property
    have hn : i.2.val + (i.1.val - i.2.val) ≤ (window primes - 1) / (L - 1) := by
      have hh := hm.2.trans hwindow
      omega
    cases flag
    · exact positive_factor_of_joint_data primes hne hprime L hL mass _ _
        ha.1 (by omega) hc hn hdata
    · exact negative_factor_of_joint_data primes hne hprime L hL mass _ _
        ha.1 (by omega) hc hn hdata

/-- The exact quantitative square-window theorem. No injectivity, kernel,
    primality, product-divisibility, or asymptotic premise is assumed. -/
theorem square_window_zero (primes : Finset ℕ)
    (hne : primes.Nonempty) (hprime : ∀ p ∈ primes, Nat.Prime p)
    (L : ℕ) (hL : 2 ≤ L) (mass : Fin L × Fin L → ℚ)
    (hsize : L ≤ degreeSum ((window primes - 1) / (L - 1)))
    (hdata : ∀ p, ∀ hp : p ∈ primes, ∀ r : Fin p × Fin p,
      jointData (fun i : Fin L × Fin L => (i.1.val : ℤ))
        (fun i => (i.2.val : ℤ)) mass p (hprime p hp).pos r = 0) : ∀ i, mass i = 0 := by
  let q := (window primes - 1) / (L - 1)
  have hq : 1 ≤ q := by
    by_cases hzero : q = 0
    · change L ≤ degreeSum q at hsize
      simp only [hzero, degreeSum, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
        Finset.sum_empty] at hsize
      omega
    · exact Nat.pos_of_ne_zero hzero
  have hfactors := all_factors_of_joint_data primes hne hprime L q (by omega) hq
    (Nat.le_refl q) mass hdata
  have hdvd := factorProduct_dvd q (generating L mass) hfactors
  have hgen : generating L mass = 0 := by
    by_contra hnonzero
    have hdegree := Polynomial.natDegree_le_of_dvd hdvd hnonzero
    rw [factorProduct_natDegree q hq] at hdegree
    have hbound := generating_natDegree_bound L (by omega) mass
    change L ≤ degreeSum q at hsize
    omega
  exact (generating_zero_iff L mass).mp hgen

end
end NearCubicGates.ProjectionBinomials

import Proof.Foundations.SupplierPipeline

/-!
# Explicit prime surrogate

This file derives the finite prime-family bounds used by Appendix A.13 from
the typed Rosser--Schoenfeld theta contract and elementary divisor counting.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierPrime

open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.ThresholdCompiler

def primesUpTo (cutoff : ℕ) : Finset ℕ :=
  (Finset.range (cutoff + 1)).filter Nat.Prime

abbrev PrimeIndex (cutoff : ℕ) := ↥(primesUpTo cutoff)

theorem mem_primesUpTo {cutoff prime : ℕ} :
    prime ∈ primesUpTo cutoff ↔ prime.Prime ∧ prime ≤ cutoff := by
  simp [primesUpTo, and_comm]

theorem chebyshevTheta_nat (cutoff : ℕ) :
    chebyshevTheta (cutoff : ℝ) =
      ∑ prime ∈ primesUpTo cutoff, Real.log prime := by
  simp [chebyshevTheta, primesUpTo]

theorem log_prime_le_log_cutoff {cutoff prime : ℕ}
    (hprime : prime ∈ primesUpTo cutoff) :
    Real.log prime ≤ Real.log cutoff := by
  have hdata := mem_primesUpTo.mp hprime
  exact Real.log_le_log
    (by exact_mod_cast hdata.1.pos)
    (by exact_mod_cast hdata.2)

theorem theta_le_card_mul_log (cutoff : ℕ) :
    chebyshevTheta (cutoff : ℝ) ≤
      ((primesUpTo cutoff).card : ℝ) * Real.log cutoff := by
  rw [chebyshevTheta_nat]
  calc
    (∑ prime ∈ primesUpTo cutoff, Real.log prime) ≤
        ∑ _prime ∈ primesUpTo cutoff, Real.log cutoff := by
      apply Finset.sum_le_sum
      intro prime hprime
      exact log_prime_le_log_cutoff hprime
    _ = ((primesUpTo cutoff).card : ℝ) * Real.log cutoff := by
      simp

theorem primeCount_lower
    (theta : PrimeThetaBoundContract) {cutoff : ℕ}
    (hcutoff : 563 ≤ cutoff) :
    (cutoff : ℝ) / (3 * Real.log cutoff) ≤
      (primesUpTo cutoff).card := by
  have hcutoffReal : (563 : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
  have hthetaLower :
      (cutoff : ℝ) / 3 ≤ chebyshevTheta (cutoff : ℝ) :=
    (theta cutoff hcutoffReal).2
  have hthetaUpper := theta_le_card_mul_log cutoff
  have hlogPositive : 0 < Real.log cutoff := by
    apply Real.log_pos
    exact_mod_cast (show 1 < cutoff by omega)
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogPositive)).2
  calc
    (cutoff : ℝ) ≤ 3 * chebyshevTheta (cutoff : ℝ) := by linarith
    _ ≤ 3 * (((primesUpTo cutoff).card : ℝ) * Real.log cutoff) := by
      nlinarith
    _ = ((primesUpTo cutoff).card : ℝ) *
        (3 * Real.log cutoff) := by ring

theorem two_pow_card_primeFactors_le (value : ℕ) :
    2 ^ value.primeFactors.card ≤
      ∏ prime ∈ value.primeFactors, prime := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro prime hprime
    positivity
  · intro prime hprime
    exact (Nat.prime_of_mem_primeFactors hprime).two_le

theorem two_pow_card_primeFactors_le_value {value : ℕ}
    (hvalue : value ≠ 0) :
    2 ^ value.primeFactors.card ≤ value := by
  exact (two_pow_card_primeFactors_le value).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hvalue)
      (Nat.prod_primeFactors_dvd value))

theorem card_primeFactors_lt_of_lt_pow {value exponent : ℕ}
    (hvalue : value ≠ 0) (hbound : value < 2 ^ exponent) :
    value.primeFactors.card < exponent := by
  have hpow :
      2 ^ value.primeFactors.card < 2 ^ exponent :=
    (two_pow_card_primeFactors_le_value hvalue).trans_lt hbound
  exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow

def badPrimes (cutoff : ℕ) (difference : ℤ) : Finset (PrimeIndex cutoff) :=
  Finset.univ.filter fun prime => (prime.val : ℤ) ∣ difference

theorem badPrimes_subset_primeFactors {cutoff : ℕ} {difference : ℤ}
    (hdifference : difference ≠ 0) :
    (badPrimes cutoff difference).image Subtype.val ⊆
      difference.natAbs.primeFactors := by
  intro prime hprime
  rcases Finset.mem_image.mp hprime with ⟨indexedPrime, hbad, rfl⟩
  have hprimeData := (mem_primesUpTo.mp indexedPrime.property).1
  have hdivInt : (indexedPrime.val : ℤ) ∣ difference :=
    (Finset.mem_filter.mp hbad).2
  have hdivNat : indexedPrime.val ∣ difference.natAbs := by
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdivInt
  exact Nat.mem_primeFactors.mpr
    ⟨hprimeData, hdivNat, Int.natAbs_ne_zero.mpr hdifference⟩

theorem badPrimes_card_le_primeFactors {cutoff : ℕ} {difference : ℤ}
    (hdifference : difference ≠ 0) :
    (badPrimes cutoff difference).card ≤
      difference.natAbs.primeFactors.card := by
  rw [← Finset.card_image_of_injective
    (badPrimes cutoff difference) Subtype.val_injective]
  exact Finset.card_le_card
    (badPrimes_subset_primeFactors hdifference)

theorem badPrimes_card_lt {cutoff exponent : ℕ} {difference : ℤ}
    (hdifference : difference ≠ 0)
    (hmagnitude : difference.natAbs < 2 ^ exponent) :
    (badPrimes cutoff difference).card < exponent := by
  exact (badPrimes_card_le_primeFactors hdifference).trans_lt
    (card_primeFactors_lt_of_lt_pow
      (Int.natAbs_ne_zero.mpr hdifference) hmagnitude)

instance {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (modulus : ℤ)
    (input : Carrier → Bool) :
    Decidable (equation.HoldsModulo modulus input) := by
  unfold LabelledEquation.HoldsModulo
  infer_instance

instance {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (input : Carrier → Bool) :
    Decidable (equation.Holds input) := by
  unfold LabelledEquation.Holds
  infer_instance

def modularEquationHolds {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) {cutoff : ℕ}
    (prime : PrimeIndex cutoff) (input : Carrier → Bool) : Bool :=
  decide (equation.HoldsModulo prime.val input)

theorem modularEquationHolds_complete
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) {cutoff : ℕ}
    (input : Carrier → Bool) (hholds : equation.Holds input) :
  ∀ prime : PrimeIndex cutoff,
      modularEquationHolds equation prime input := by
  intro prime
  unfold modularEquationHolds
  apply decide_eq_true
  exact equation.holdsModulo_of_holds prime.val input hholds

theorem modularEquation_accepting_card
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) {cutoff : ℕ}
    (input : Carrier → Bool) :
    (Finset.univ.filter fun prime : PrimeIndex cutoff =>
      modularEquationHolds equation prime input).card =
        (badPrimes cutoff (equation.difference input)).card := by
  congr 1
  ext prime
  simp only [badPrimes, Finset.mem_filter, Finset.mem_univ, true_and,
    modularEquationHolds]
  constructor
  · intro hmod
    have hzero :
        equation.difference input % (prime.val : ℤ) = 0 := by
      exact of_decide_eq_true hmod
    exact Int.dvd_iff_emod_eq_zero.mpr hzero
  · intro hdiv
    apply decide_eq_true
    exact Int.dvd_iff_emod_eq_zero.mp hdiv

theorem modularEquation_sound
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) {cutoff exponent : ℕ}
    (input : Carrier → Bool)
    (hdifference : equation.difference input ≠ 0)
    (hmagnitude : (equation.difference input).natAbs < 2 ^ exponent) :
    booleanMean (fun prime : PrimeIndex cutoff =>
      modularEquationHolds equation prime input) ≤
        (exponent : ℝ) / (primesUpTo cutoff).card := by
  unfold booleanMean
  rw [show (∑ prime : PrimeIndex cutoff,
      bitAsReal (modularEquationHolds equation prime input)) =
        ((Finset.univ.filter fun prime : PrimeIndex cutoff =>
          modularEquationHolds equation prime input).card : ℝ) by
    simp [bitAsReal, Finset.sum_boole]]
  rw [modularEquation_accepting_card]
  simp only [Fintype.card_coe]
  have hcard :
      ((badPrimes cutoff (equation.difference input)).card : ℝ) ≤ exponent := by
    exact_mod_cast Nat.le_of_lt
      (badPrimes_card_lt hdifference hmagnitude)
  apply div_le_div_of_nonneg_right hcard
  positivity

theorem modularEquation_sound_from_theta
    (theta : PrimeThetaBoundContract)
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) {cutoff exponent : ℕ}
    (hcutoff : 563 ≤ cutoff)
    (input : Carrier → Bool)
    (hdifference : equation.difference input ≠ 0)
    (hmagnitude : (equation.difference input).natAbs < 2 ^ exponent) :
    booleanMean (fun prime : PrimeIndex cutoff =>
      modularEquationHolds equation prime input) ≤
        (exponent : ℝ) * (3 * Real.log cutoff) / cutoff := by
  have hbase :=
    modularEquation_sound equation (cutoff := cutoff)
      input hdifference hmagnitude
  have hcount := primeCount_lower theta hcutoff
  have hcutoffPositive : (0 : ℝ) < cutoff := by positivity
  have hlogPositive : 0 < Real.log cutoff := by
    apply Real.log_pos
    exact_mod_cast (show 1 < cutoff by omega)
  have hprimeCountPositive :
      (0 : ℝ) < (primesUpTo cutoff).card := by
    have hlowerPositive :
        (0 : ℝ) < (cutoff : ℝ) / (3 * Real.log cutoff) := by positivity
    exact lt_of_lt_of_le hlowerPositive hcount
  calc
    booleanMean (fun prime : PrimeIndex cutoff =>
        modularEquationHolds equation prime input) ≤
        (exponent : ℝ) / (primesUpTo cutoff).card := hbase
    _ ≤ (exponent : ℝ) /
        ((cutoff : ℝ) / (3 * Real.log cutoff)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hcount
    _ = (exponent : ℝ) * (3 * Real.log cutoff) / cutoff := by
      field_simp

/-- A syntax-derived absolute bound for one equation difference on the Boolean
cube.  It is intentionally coarse but total and requires no caller proof. -/
def equationMagnitudeBound {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) : ℕ :=
  (∑ index, (equation.weights index).natAbs) + equation.target.natAbs

theorem equation_difference_natAbs_le_magnitudeBound
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (input : Carrier → Bool) :
    (equation.difference input).natAbs ≤
      equationMagnitudeBound equation := by
  unfold LabelledEquation.difference LabelledEquation.score
    equationMagnitudeBound
  calc
    ((∑ index, equation.weights index * bitInt (input index)) -
        equation.target).natAbs ≤
        (∑ index, equation.weights index *
          bitInt (input index)).natAbs + equation.target.natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ (∑ index,
          (equation.weights index * bitInt (input index)).natAbs) +
            equation.target.natAbs := by
      gcongr
      exact Int.natAbs_sum_le Finset.univ _
    _ ≤ (∑ index, (equation.weights index).natAbs) +
          equation.target.natAbs := by
      gcongr with index
      cases input index <;> simp [bitInt]

/-- Sum envelope for a finite emitted equation family.  Summation avoids an
extra maximum/default branch and is monotone for every family member. -/
def familyMagnitudeBound
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier) : ℕ :=
  ∑ equation, equationMagnitudeBound (realize equation)

theorem equationMagnitudeBound_le_family
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (equation : Equation) :
    equationMagnitudeBound (realize equation) ≤
      familyMagnitudeBound realize := by
  classical
  unfold familyMagnitudeBound
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le
      (equationMagnitudeBound (realize candidate)))
    (Finset.mem_univ equation)

/-- Minimal binary exponent whose range strictly contains the complete finite
equation-family envelope. -/
def familyMagnitudeExponent
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier) : ℕ :=
  Nat.clog 2 (familyMagnitudeBound realize + 1)

theorem family_difference_lt_two_pow
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (equation : Equation) (input : Carrier → Bool) :
    ((realize equation).difference input).natAbs <
      2 ^ familyMagnitudeExponent realize := by
  calc
    ((realize equation).difference input).natAbs ≤
        equationMagnitudeBound (realize equation) :=
      equation_difference_natAbs_le_magnitudeBound _ _
    _ ≤ familyMagnitudeBound realize :=
      equationMagnitudeBound_le_family realize equation
    _ < familyMagnitudeBound realize + 1 := Nat.lt_succ_self _
    _ ≤ 2 ^ familyMagnitudeExponent realize := by
      exact Nat.le_pow_clog (by omega) _

/-- Polynomial cutoff scale large enough for both the theta onset and a
requested reciprocal error denominator. -/
def canonicalPrimeScale (exponent denominator : ℕ) : ℕ :=
  max 24 (6 * (exponent + 1) * (denominator + 1))

def canonicalPrimeCutoff (exponent denominator : ℕ) : ℕ :=
  canonicalPrimeScale exponent denominator ^ 2

theorem canonicalPrimeCutoff_ge_563 (exponent denominator : ℕ) :
    563 ≤ canonicalPrimeCutoff exponent denominator := by
  unfold canonicalPrimeCutoff canonicalPrimeScale
  have hscale : 24 ≤
      max 24 (6 * (exponent + 1) * (denominator + 1)) :=
    le_max_left _ _
  nlinarith

theorem canonicalPrimeError_le (exponent denominator : ℕ) :
    (exponent : ℝ) *
          (3 * Real.log (canonicalPrimeCutoff exponent denominator)) /
        canonicalPrimeCutoff exponent denominator ≤
      1 / (denominator + 1 : ℕ) := by
  let scale := canonicalPrimeScale exponent denominator
  have hscaleNat :
      6 * (exponent + 1) * (denominator + 1) ≤ scale := by
    exact le_max_right _ _
  have hscalePositiveNat : 0 < scale := by
    exact lt_of_lt_of_le (by omega) (le_max_left 24 _)
  have hscalePositive : (0 : ℝ) < scale := by
    exact_mod_cast hscalePositiveNat
  have hdenominatorPositive :
      (0 : ℝ) < (denominator + 1 : ℕ) := by
    positivity
  have hlog :
      Real.log (canonicalPrimeCutoff exponent denominator) ≤
        2 * scale := by
    rw [show (canonicalPrimeCutoff exponent denominator : ℝ) =
      (scale : ℝ) ^ 2 by
        simp [canonicalPrimeCutoff, scale]]
    rw [Real.log_pow]
    have := Real.log_le_self hscalePositive.le
    norm_num
    gcongr
  have hscaleLower :
      (6 : ℝ) * exponent * (denominator + 1 : ℕ) ≤ scale := by
    have hnat :
        6 * exponent * (denominator + 1) ≤ scale :=
      (Nat.mul_le_mul_right (denominator + 1)
        (Nat.mul_le_mul_left 6 (Nat.le_succ exponent))).trans hscaleNat
    exact_mod_cast hnat
  calc
    (exponent : ℝ) *
          (3 * Real.log (canonicalPrimeCutoff exponent denominator)) /
        canonicalPrimeCutoff exponent denominator ≤
        (exponent : ℝ) * (3 * (2 * scale)) /
          canonicalPrimeCutoff exponent denominator := by
      gcongr
    _ = ((6 : ℝ) * exponent) / scale := by
      rw [show (canonicalPrimeCutoff exponent denominator : ℝ) =
        (scale : ℝ) ^ 2 by
          simp [canonicalPrimeCutoff, scale]]
      field_simp
      ring
    _ ≤ 1 / (denominator + 1 : ℕ) := by
      rw [div_le_div_iff₀ hscalePositive hdenominatorPositive]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaleLower

/-- A complete prime-surrogate certificate for one represented equation
family.  The magnitude obligation ranges only over equations the compiler can
emit; requiring it for every integer equation would be uninhabitable. -/
noncomputable def primeSurrogateCertificateFor
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier]
    (realize : Equation → LabelledEquation Carrier)
    {cutoff exponent : ℕ} (hcutoff : 563 ≤ cutoff)
    (hmagnitude : ∀ (equation : Equation) (input : Carrier → Bool),
      ((realize equation).difference input).natAbs < 2 ^ exponent) :
    PrimeSurrogateCertificate
      Equation (PrimeIndex cutoff) (Carrier → Bool) where
  cardPositive := by
    simp only [Fintype.card_coe]
    apply Finset.card_pos.mpr
    refine ⟨2, ?_⟩
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  exact equation input := decide ((realize equation).Holds input)
  modular equation prime input :=
    modularEquationHolds (realize equation) prime input
  error := (exponent : ℝ) * (3 * Real.log cutoff) / cutoff
  errorNonnegative := by
    have hlog : 0 ≤ Real.log cutoff := by
      exact (Real.log_nonneg (by exact_mod_cast (show 1 ≤ cutoff by omega)))
    positivity
  complete := by
    intro equation input hexact prime
    have hholds : (realize equation).Holds input :=
      of_decide_eq_true hexact
    exact modularEquationHolds_complete
      (realize equation) input hholds prime
  sound := by
    intro equation input hexact
    have hnotHolds : ¬(realize equation).Holds input := by
      intro hholds
      exact hexact (decide_eq_true hholds)
    have hdifference : (realize equation).difference input ≠ 0 := hnotHolds
    exact modularEquation_sound_from_theta theta
      (realize equation) hcutoff input
      hdifference (hmagnitude equation input)

/-- Canonical cutoff closure.  Callers choose a desired scale, while the
Rosser--Schoenfeld onset is enforced internally and cannot be forgotten. -/
noncomputable def canonicalPrimeSurrogateCertificateFor
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier]
    (realize : Equation → LabelledEquation Carrier)
    (requestedCutoff exponent : ℕ)
    (hmagnitude : ∀ (equation : Equation) (input : Carrier → Bool),
      ((realize equation).difference input).natAbs < 2 ^ exponent) :
    PrimeSurrogateCertificate Equation
      (PrimeIndex (max 563 requestedCutoff)) (Carrier → Bool) :=
  primeSurrogateCertificateFor theta realize (le_max_left _ _) hmagnitude

/-- Fully closed finite-family prime surrogate: both the magnitude exponent
and the imported theta onset are computed from the represented equations. -/
noncomputable def finiteFamilyPrimeSurrogateCertificate
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (requestedCutoff : ℕ) :
    PrimeSurrogateCertificate Equation
      (PrimeIndex (max 563 requestedCutoff)) (Carrier → Bool) :=
  canonicalPrimeSurrogateCertificateFor theta realize requestedCutoff
    (familyMagnitudeExponent realize)
    (family_difference_lt_two_pow realize)

/-- Fully parameterized finite-family certificate with reciprocal error
`1 / (denominator + 1)` and no numeric side conditions. -/
noncomputable def tunedFiniteFamilyPrimeSurrogateCertificate
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (denominator : ℕ) :
    PrimeSurrogateCertificate Equation
      (PrimeIndex
        (canonicalPrimeCutoff
          (familyMagnitudeExponent realize) denominator))
      (Carrier → Bool) :=
  primeSurrogateCertificateFor theta realize
    (canonicalPrimeCutoff_ge_563 _ _)
    (family_difference_lt_two_pow realize)

theorem tunedFiniteFamilyPrimeSurrogateCertificate_error_le
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (denominator : ℕ) :
    (tunedFiniteFamilyPrimeSurrogateCertificate theta realize denominator).error ≤
      1 / (denominator + 1 : ℕ) := by
  exact canonicalPrimeError_le (familyMagnitudeExponent realize) denominator

noncomputable def inversePolynomialPrimeDenominator
    (q : ℕ) (accuracyExponent : ℝ) : ℕ :=
  ⌈Real.rpow (q : ℝ) accuracyExponent⌉₊

/-- Prime surrogate specialized to the public A.1 error scale. -/
noncomputable def inversePolynomialFiniteFamilyPrimeSurrogateCertificate
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (q : ℕ) (accuracyExponent : ℝ) :
    PrimeSurrogateCertificate Equation
      (PrimeIndex
        (canonicalPrimeCutoff (familyMagnitudeExponent realize)
          (inversePolynomialPrimeDenominator q accuracyExponent)))
      (Carrier → Bool) :=
  tunedFiniteFamilyPrimeSurrogateCertificate theta realize
    (inversePolynomialPrimeDenominator q accuracyExponent)

theorem inversePolynomialFiniteFamilyPrime_error_le
    (theta : PrimeThetaBoundContract)
    {Carrier Equation : Type} [Fintype Carrier] [Fintype Equation]
    (realize : Equation → LabelledEquation Carrier)
    (q : ℕ) (accuracyExponent : ℝ) (hq : 0 < q) :
    (inversePolynomialFiniteFamilyPrimeSurrogateCertificate
        theta realize q accuracyExponent).error ≤
      inversePolynomialAdvantage q accuracyExponent := by
  let denominator :=
    inversePolynomialPrimeDenominator q accuracyExponent
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hrpowPositive :
      0 < Real.rpow (q : ℝ) accuracyExponent :=
    Real.rpow_pos_of_pos hqReal _
  have hrpowLe :
      Real.rpow (q : ℝ) accuracyExponent ≤
        (denominator + 1 : ℕ) := by
    calc
      Real.rpow (q : ℝ) accuracyExponent ≤
          (denominator : ℕ) := by
        exact Nat.le_ceil _
      _ ≤ (denominator + 1 : ℕ) := by
        exact_mod_cast Nat.le_succ denominator
  calc
    (inversePolynomialFiniteFamilyPrimeSurrogateCertificate
        theta realize q accuracyExponent).error ≤
        1 / (denominator + 1 : ℕ) := by
      exact tunedFiniteFamilyPrimeSurrogateCertificate_error_le
        theta realize denominator
    _ ≤ 1 / Real.rpow (q : ℝ) accuracyExponent :=
      one_div_le_one_div_of_le hrpowPositive hrpowLe
    _ = inversePolynomialAdvantage q accuracyExponent := by
      unfold inversePolynomialAdvantage
      simpa [one_div] using
        (Real.rpow_neg hqReal.le accuracyExponent).symm

end NearCubicWires.SupplierPrime

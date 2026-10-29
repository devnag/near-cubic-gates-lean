import Std

/-!
# Arithmetic used by the certified counter

This file proves the witness-independent digit identity, injectivity of
modular reduction on a short integer interval, and finite moment tests.
-/

namespace NearCubicGates.CountingCore

/-! ## Arbitrary proposed chains, including unsampled proposals -/

def proposedDigit (rate value : Nat → Int) : Nat → Int
  | 0 => value 0
  | j + 1 => value (j + 1) - rate j * value j

def reconstruct (rate digit : Nat → Int) : Nat → Int
  | 0 => digit 0
  | j + 1 => rate j * reconstruct rate digit j + digit (j + 1)

/-- The telescoping identity holds for every proposed coefficient sequence;
it requires neither sampling nor probabilistic consistency. -/
theorem reconstruct_proposedDigit (rate value : Nat → Int) (j : Nat) :
    reconstruct rate (proposedDigit rate value) j = value j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [reconstruct, proposedDigit, ih]
    omega

def evaluateSteps (initial : Int) : List (Int × Int) → Int
  | [] => initial
  | (a, e) :: steps => evaluateSteps (a * initial + e) steps

def rateProduct : List (Int × Int) → Int
  | [] => 1
  | (a, _) :: steps => rateProduct steps * a

def weightedDigits : List (Int × Int) → Int
  | [] => 0
  | (_, e) :: steps => rateProduct steps * e + weightedDigits steps

/-- Explicit weighted form of the same telescoping identity. -/
theorem evaluateSteps_eq_weighted (initial : Int) (steps : List (Int × Int)) :
    evaluateSteps initial steps = rateProduct steps * initial + weightedDigits steps := by
  induction steps generalizing initial with
  | nil => simp [evaluateSteps, rateProduct, weightedDigits]
  | cons step steps ih =>
    rcases step with ⟨a, e⟩
    simp [evaluateSteps, rateProduct, weightedDigits, ih,
      Int.mul_add, Int.mul_assoc, Int.add_assoc]

/-! ## A short digit is uniquely determined by its residue -/

/-- Modular reduction is injective on any integer interval of length `< p`.
The interval need not begin at zero, and `a`, `b`, and `lo` may be negative. -/
theorem short_interval_residue_unique
    (a b lo p : Int)
    (ha0 : 0 ≤ a - lo) (hb0 : 0 ≤ b - lo)
    (ha : a - lo < p) (hb : b - lo < p)
    (hmod : a % p = b % p) : a = b := by
  have hs : (a - lo) % p = (b - lo) % p := by
    rw [Int.sub_emod a lo p, Int.sub_emod b lo p, hmod]
  rw [Int.emod_eq_of_lt ha0 ha, Int.emod_eq_of_lt hb0 hb] at hs
  omega

theorem short_interval_residue_iff
    (a b lo p : Int)
    (ha0 : 0 ≤ a - lo) (hb0 : 0 ≤ b - lo)
    (ha : a - lo < p) (hb : b - lo < p) :
    a % p = b % p ↔ a = b := by
  constructor
  · exact short_interval_residue_unique a b lo p ha0 hb0 ha hb
  · intro h
    exact congrArg (fun z => z % p) h

/-- The centered, strict digit window of `sec:algorithm`, "Reconstruction inside a certified cell". -/
theorem centered_digit_residue_unique
    (a b center h p : Int)
    (haL : center - h < a) (haU : a < center + h)
    (hbL : center - h < b) (hbU : b < center + h)
    (hwidth : 2 * h - 1 ≤ p)
    (hmod : a % p = b % p) : a = b := by
  apply short_interval_residue_unique a b (center - h + 1) p
  · omega
  · omega
  · omega
  · omega
  · exact hmod

/-! ## Exact finite moment certificates

We sum powers of natural magnitudes.  For integer-valued samples the
canonical magnitude is `Int.natAbs`; in particular, even powers have
these magnitudes. No bound is inferred from sampled observations.
-/

def powerSum (exponent : Nat) : List Nat → Nat
  | [] => 0
  | value :: values => value ^ exponent + powerSum exponent values

theorem power_mono {a b : Nat} (hab : a ≤ b) (exponent : Nat) :
    a ^ exponent ≤ b ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
    simpa [Nat.pow_succ] using Nat.mul_le_mul ih hab

theorem member_power_le_sum (exponent value : Nat) (values : List Nat)
    (hmem : value ∈ values) : value ^ exponent ≤ powerSum exponent values := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
    simp only [List.mem_cons] at hmem
    simp only [powerSum]
    rcases hmem with h | h
    · subst value
      omega
    · have ht := ih h
      omega

/-- Soundness: one out-of-range sample would already violate the moment test. -/
theorem powerSum_lt_certifies (exponent radius : Nat) (values : List Nat)
    (htest : powerSum exponent values < radius ^ exponent) :
    ∀ value ∈ values, value < radius := by
  intro value hmem
  have hs := member_power_le_sum exponent value values hmem
  by_cases hsmall : value < radius
  · exact hsmall
  · have hr : radius ≤ value := by omega
    have hp := power_mono hr exponent
    omega

theorem powerSum_le_length (exponent bound : Nat) (values : List Nat)
    (hbound : ∀ value ∈ values, value ≤ bound) :
    powerSum exponent values ≤ values.length * bound ^ exponent := by
  induction values with
  | nil => simp [powerSum]
  | cons head tail ih =>
    have hh : head ≤ bound := hbound head (by simp)
    have ht : ∀ value ∈ tail, value ≤ bound := by
      intro value hmem
      exact hbound value (by simp [hmem])
    have hs := ih ht
    have hp := power_mono hh exponent
    simp only [powerSum, List.length_cons, Nat.succ_mul]
    omega

/-- Completeness in exact arithmetic: a uniform smaller pointwise bound,
with enough numerical slack, implies the strict moment test. -/
theorem powerSum_lt_of_uniform_bound
    (exponent bound radius : Nat) (values : List Nat)
    (hbound : ∀ value ∈ values, value ≤ bound)
    (hslack : values.length * bound ^ exponent < radius ^ exponent) :
    powerSum exponent values < radius ^ exponent := by
  have hs := powerSum_le_length exponent bound values hbound
  omega

theorem integer_magnitudes_certified
    (k radius : Nat) (values : List Int)
    (htest : powerSum (2 * k) (values.map Int.natAbs) < radius ^ (2 * k)) :
    ∀ value ∈ values, value.natAbs < radius := by
  intro value hmem
  apply powerSum_lt_certifies (2 * k) radius (values.map Int.natAbs) htest
  exact List.mem_map.mpr ⟨value, hmem, rfl⟩

def integerPowerSum (exponent : Nat) : List Int → Int
  | [] => 0
  | value :: values => value ^ exponent + integerPowerSum exponent values

theorem even_power_eq_magnitude (value : Int) (k : Nat) :
    value ^ (2 * k) = ((value.natAbs ^ (2 * k) : Nat) : Int) := by
  rw [← Int.natAbs_pow]
  exact Int.eq_natAbs_of_nonneg (Int.pow_nonneg_of_even (by omega))

theorem integerPowerSum_even (k : Nat) (values : List Int) :
    integerPowerSum (2 * k) values =
      ((powerSum (2 * k) (values.map Int.natAbs) : Nat) : Int) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [integerPowerSum, List.map_cons, powerSum, Int.natCast_add,
      even_power_eq_magnitude, ih]

/-- The integer even-power moment appearing literally in `lem:moment`
certifies every integer sample's magnitude. -/
theorem integer_even_moment_certifies
    (k radius : Nat) (values : List Int)
    (htest : integerPowerSum (2 * k) values < (radius : Int) ^ (2 * k)) :
    ∀ value ∈ values, value.natAbs < radius := by
  rw [integerPowerSum_even] at htest
  change ((powerSum (2 * k) (values.map Int.natAbs) : Nat) : Int) <
    ((radius ^ (2 * k) : Nat) : Int) at htest
  exact integer_magnitudes_certified k radius values (Int.ofNat_lt.mp htest)

end NearCubicGates.CountingCore

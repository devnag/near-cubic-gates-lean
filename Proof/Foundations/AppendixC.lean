import Mathlib

/-!
# Local Appendix-C arithmetic and quantifier lemmas

These theorems formalize finite componentwise error propagation, exact schedule
crossings, common-language quantifier assembly, one-extra-log multiplier
absorption, and the two-bit XOR basis used by the transfer.  PCP, refuter, and
amplification theorems remain explicit source contracts.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.AppendixC

inductive Mode where
  | symmetric
  | threshold
deriving DecidableEq, Repr

theorem leastCrossingIsExact
    (mu : ℕ → ℕ) (n m : ℕ)
    (hprev : mu (n - 1) < m)
    (hcross : m ≤ mu n)
    (hjump : mu n ≤ mu (n - 1) + 1) :
    mu n = m := by
  omega

/-- If the first scheduled core above `n/2` is only `n/6` beyond the
preceding core, maximality places the preceding core strictly above `n/3`.
This is the algebraic heart of the cofinal padding interval in Appendix C.12;
the manuscript separately proves that its actual schedule jump is `o(n)`. -/
theorem maximalCoreAboveThird
    (n core next : ℚ)
    (hcross : n / 2 < next)
    (hjump : next - core ≤ n / 6) :
    n / 3 < core := by
  linarith

/-- For integer advantage exponent `c`, a core within a factor three of the
target has the padding reserve `core^(-(c+1)) < target^(-c)` once
`core > 3^c`.  This division-free form is what the asymptotic prose uses. -/
theorem integerPaddingAdvantageReserve
    (target core c : ℕ)
    (hcore : 0 < core)
    (hratio : target ≤ 3 * core)
    (hlarge : 3 ^ c < core) :
    target ^ c < core ^ (c + 1) := by
  calc
    target ^ c ≤ (3 * core) ^ c := Nat.pow_le_pow_left hratio c
    _ = 3 ^ c * core ^ c := by rw [mul_pow]
    _ < core * core ^ c :=
      (Nat.mul_lt_mul_right (pow_pos hcore c)).2 hlarge
    _ = core ^ (c + 1) := by simp [pow_succ, Nat.mul_comm]

theorem completenessEstimateAboveThreshold
    (complete sound error : ℚ)
    (hgap : 0 < complete - sound)
    (herror : error ≤ (complete - sound) / 40) :
    complete - 3 * error / 2 > complete - (complete - sound) / 3 := by
  linarith

theorem soundnessEstimateBelowThreshold
    (complete sound bad error : ℚ)
    (hgap : 0 < complete - sound)
    (hbad : bad ≤ (complete - sound) / 8)
    (herror : error ≤ (complete - sound) / 40) :
    sound + bad + 3 * error / 2 < complete - (complete - sound) / 3 := by
  linarith

theorem componentwiseErrorBound
    {ι : Type} (index : Finset ι)
    (coefficient exact estimate : ι → ℚ) (error mass : ℚ)
    (herror : 0 ≤ error)
    (hpoint : ∀ i ∈ index, |estimate i - exact i| ≤ error)
    (hmass : (∑ i ∈ index, |coefficient i|) ≤ mass) :
    |(∑ i ∈ index, coefficient i * estimate i) -
        (∑ i ∈ index, coefficient i * exact i)| ≤ error * mass := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ i ∈ index, coefficient i * (estimate i - exact i)|
        ≤ ∑ i ∈ index, |coefficient i * (estimate i - exact i)| :=
          abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ index, |coefficient i| * |estimate i - exact i| := by
          apply sum_congr rfl
          intro i _
          rw [abs_mul]
    _ ≤ ∑ i ∈ index, |coefficient i| * error := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hpoint i hi) (abs_nonneg _)
    _ = error * (∑ i ∈ index, |coefficient i|) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro i _
          ring
    _ ≤ error * mass := mul_le_mul_of_nonneg_left hmass herror

theorem oneExtraLogAbsorbsMultiplier
    (multiplier coefficient logValue scale : ℚ)
    (hlog : 0 < logValue)
    (hscale : 0 < scale)
    (hdominate : multiplier < coefficient * logValue) :
    scale * (multiplier / logValue) < scale * coefficient := by
  have hratio : multiplier / logValue < coefficient := by
    exact (div_lt_iff₀ hlog).2 hdominate
  exact mul_lt_mul_of_pos_left hratio hscale

def EventuallyHard {Language : Type}
    (hard : Language → Mode → ℕ → Prop) (language : Language) : Prop :=
  ∃ onset, ∀ n, onset ≤ n → ∀ mode, hard language mode n

theorem combineCommonLanguage
    {Language : Type} (hard : Language → Mode → ℕ → Prop)
    (language : Language)
    (hsym : ∃ onset, ∀ n, onset ≤ n → hard language Mode.symmetric n)
    (hthr : ∃ onset, ∀ n, onset ≤ n → hard language Mode.threshold n) :
    EventuallyHard hard language := by
  rcases hsym with ⟨symOnset, hsym⟩
  rcases hthr with ⟨thrOnset, hthr⟩
  refine ⟨max symOnset thrOnset, ?_⟩
  intro n hn mode
  cases mode with
  | symmetric =>
      exact hsym n (le_trans (le_max_left _ _) hn)
  | threshold =>
      exact hthr n (le_trans (le_max_right _ _) hn)

def agreementQ (left right : Bool) : ℚ :=
  if left = right then 1 else 0

def sliceAgreement
    {Input Padding : Type} [Fintype Input]
    (circuit : Padding → Input → Bool) (target : Input → Bool)
    (padding : Padding) : ℚ :=
  𝔼 input, agreementQ (circuit padding input) (target input)

def paddedAgreement
    {Input Padding : Type} [Fintype Input] [Fintype Padding]
    (circuit : Padding → Input → Bool) (target : Input → Bool) : ℚ :=
  𝔼 padding, sliceAgreement circuit target padding

/-- Averaging over ignored variables yields a restriction with at least the
original agreement.  This is the exact finite statement used when a scheduled
hard core is padded to the requested target length. -/
theorem existsRestrictionPreservingAgreement
    {Input Padding : Type} [Fintype Input] [Fintype Padding] [Nonempty Padding]
    (circuit : Padding → Input → Bool) (target : Input → Bool) :
    ∃ padding, paddedAgreement circuit target ≤
      sliceAgreement circuit target padding := by
  have hself :
      paddedAgreement circuit target ≤
        𝔼 padding : Padding, sliceAgreement circuit target padding := le_rfl
  obtain ⟨padding, _, hpadding⟩ :=
    Finset.exists_le_of_le_expect
      (s := (Finset.univ : Finset Padding)) Finset.univ_nonempty hself
  exact ⟨padding, hpadding⟩

def bitQ (b : Bool) : ℚ := if b then 1 else 0

def table4 (q00 q01 q10 q11 u v : Bool) : Bool :=
  if u then (if v then q11 else q10) else (if v then q01 else q00)

def alpha0 (q00 : Bool) : ℚ := bitQ q00

def alpha1 (q00 q01 q10 q11 : Bool) : ℚ :=
  (bitQ q10 + bitQ q11 - bitQ q00 - bitQ q01) / 2

def alpha2 (q00 q01 q10 q11 : Bool) : ℚ :=
  (bitQ q01 + bitQ q11 - bitQ q00 - bitQ q10) / 2

def alphaXor (q00 q01 q10 q11 : Bool) : ℚ :=
  (bitQ q10 + bitQ q01 - bitQ q00 - bitQ q11) / 2

theorem xorBasisReconstruction
    (q00 q01 q10 q11 u v : Bool) :
    bitQ (table4 q00 q01 q10 q11 u v) =
      alpha0 q00
        + alpha1 q00 q01 q10 q11 * bitQ u
        + alpha2 q00 q01 q10 q11 * bitQ v
        + alphaXor q00 q01 q10 q11 * bitQ (xor u v) := by
  cases q00 <;> cases q01 <;> cases q10 <;> cases q11 <;>
    cases u <;> cases v <;>
    norm_num [bitQ, table4, alpha0, alpha1, alpha2, alphaXor]

theorem nonconstantCoefficientMassLeThreeHalves
    (q00 q01 q10 q11 : Bool) :
    |alpha1 q00 q01 q10 q11|
        + |alpha2 q00 q01 q10 q11|
        + |alphaXor q00 q01 q10 q11| ≤ (3 : ℚ) / 2 := by
  cases q00 <;> cases q01 <;> cases q10 <;> cases q11 <;>
    norm_num [bitQ, alpha1, alpha2, alphaXor, abs_of_nonneg, abs_of_nonpos]

end NearCubicWires.AppendixC

import Proof.Gates.PublicSamplingRates
import Proof.Gates.CertifiedScoreSupport

/-! A genuinely sampled good chain passes the same literal moment tests
    used for arbitrary-proposal soundness. The concentration event remains
    explicit here; finite probability selection is a separate obligation. -/

set_option autoImplicit false

namespace NearCubicGates.SampledChainMoments

open scoped BigOperators
open PublicSamplingRates NestedRateChain CountingCore CertifiedScoreSupport

variable {Points : Type*}

def delta (values : Points → ℕ → ℤ) (reference x : Points) (j : ℕ) : ℝ :=
  (values x j - values reference j : ℤ)

def scoreDelta (score : Points → ℤ) (reference x : Points) : ℝ :=
  (score x - score reference : ℤ)

theorem first_digit_small (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (values : Points → ℕ → ℤ) (score : Points → ℤ) (reference x : Points)
    (hscore : |scoreDelta score reference x| ≤ liveCap T h ℓ)
    (hsampled : |delta values reference x 0 - rate T h ℓ 0 * scoreDelta score reference x| ≤
      fluctuation T h ℓ (rate T h ℓ 0)) :
    |delta values reference x 0| ≤ h / 2 := by
  have hr := (all_rates_bounded T h ℓ hT hh 0).1
  calc
    _ = |(delta values reference x 0 - rate T h ℓ 0 * scoreDelta score reference x) +
        rate T h ℓ 0 * scoreDelta score reference x| := by congr 1; ring
    _ ≤ |delta values reference x 0 - rate T h ℓ 0 * scoreDelta score reference x| +
        |rate T h ℓ 0 * scoreDelta score reference x| := abs_add_le _ _
    _ ≤ fluctuation T h ℓ (rate T h ℓ 0) + rate T h ℓ 0 * liveCap T h ℓ := by
      rw [abs_mul, abs_of_pos hr]
      exact add_le_add hsampled (mul_le_mul_of_nonneg_left hscore hr.le)
    _ ≤ h / 2 := by have hb := initial_digit_bound T h ℓ hT hh; linarith

theorem public_rate_recurrence (T h ℓ : ℝ) (j : ℕ)
    (ha : rateRatio (initialRatio T h ℓ) j < 1 / 256) :
    rate T h ℓ (j + 1) = (factor (rateRatio (initialRatio T h ℓ) j) : ℝ) * rate T h ℓ j := by
  unfold rate
  simp only [rateRatio, if_pos ha, next]
  ring

theorem correction_digit_small (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (values : Points → ℕ → ℤ) (score : Points → ℤ) (reference x : Points) (j : ℕ)
    (ha : rateRatio (initialRatio T h ℓ) j < 1 / 256)
    (hsampled : ∀ i ∈ ({j, j + 1} : Finset ℕ),
      |delta values reference x i - rate T h ℓ i * scoreDelta score reference x| ≤
        fluctuation T h ℓ (rate T h ℓ i)) :
    |delta values reference x (j + 1) -
        (factor (rateRatio (initialRatio T h ℓ) j) : ℝ) * delta values reference x j| ≤ h / 2 := by
  let a : ℝ := factor (rateRatio (initialRatio T h ℓ) j)
  have ha0 : 0 ≤ a := by positivity
  have heq : delta values reference x (j + 1) - a * delta values reference x j =
      (delta values reference x (j + 1) - rate T h ℓ (j + 1) * scoreDelta score reference x) -
        a * (delta values reference x j - rate T h ℓ j * scoreDelta score reference x) := by
    rw [public_rate_recurrence T h ℓ j ha]
    dsimp [a]
    ring
  change |delta values reference x (j + 1) - a * delta values reference x j| ≤ h / 2
  rw [heq]
  calc
    _ ≤ |delta values reference x (j + 1) - rate T h ℓ (j + 1) * scoreDelta score reference x| +
        |a * (delta values reference x j - rate T h ℓ j * scoreDelta score reference x)| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le
          (delta values reference x (j + 1) - rate T h ℓ (j + 1) * scoreDelta score reference x)
          (-(a * (delta values reference x j - rate T h ℓ j * scoreDelta score reference x))))
    _ ≤ fluctuation T h ℓ (rate T h ℓ (j + 1)) + a * fluctuation T h ℓ (rate T h ℓ j) := by
      rw [abs_mul, abs_of_nonneg ha0]
      exact add_le_add (hsampled _ (by simp))
        (mul_le_mul_of_nonneg_left (hsampled _ (by simp)) ha0)
    _ ≤ h / 2 := correction_digit_bound T h ℓ hT hh j ha

theorem good_chain_digits_small (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (values : Points → ℕ → ℤ) (score : Points → ℤ) (reference x : Points) (J : ℕ)
    (hactive : ∀ j, j < J → rateRatio (initialRatio T h ℓ) j < 1 / 256)
    (hscore : |scoreDelta score reference x| ≤ liveCap T h ℓ)
    (hsampled : ∀ j, j ≤ J →
      |delta values reference x j - rate T h ℓ j * scoreDelta score reference x| ≤
        fluctuation T h ℓ (rate T h ℓ j)) :
    ∀ j, j ≤ J →
      |((proposedDigit (fun i => (factor (rateRatio (initialRatio T h ℓ) i) : ℤ))
          (values x) j -
        proposedDigit (fun i => (factor (rateRatio (initialRatio T h ℓ) i) : ℤ))
          (values reference) j : ℤ) : ℝ)| ≤ h / 2 := by
  intro j hj
  cases j with
  | zero => exact first_digit_small T h ℓ hT hh values score reference x hscore (hsampled 0 (by omega))
  | succ j =>
      have hb := correction_digit_small T h ℓ hT hh values score reference x j (hactive j (by omega))
        (fun i hi => hsampled i (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega))
      convert hb using 1
      congr 1
      simp only [proposedDigit, delta, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      ring

end NearCubicGates.SampledChainMoments

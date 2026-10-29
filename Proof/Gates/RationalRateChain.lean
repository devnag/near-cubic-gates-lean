import Proof.Gates.PublicSamplingRates
import Mathlib.Data.Rat.Floor

/-! Executable rational rates. The mathematical square root is replaced by
    the finite integer comparison prescribed in `sec:finite`. This is a
    computable Lean function. -/

set_option autoImplicit false

namespace NearCubicGates.RationalRateChain

open NestedRateChain

def factorRat (x : ℚ) : ℕ :=
  Nat.findGreatest (fun a => 16 * (a : ℚ) ^ 2 * x ≤ 1) ⌈1 / x⌉₊

theorem factorRat_eq (x : ℚ) (hx : 0 < x) (hsmall : x < 1 / 256) :
    factorRat x = factor (x : ℝ) := by
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hsr : (x : ℝ) < 1 / 256 := by
    have hc : (x : ℝ) < ((1 / 256 : ℚ) : ℝ) := Rat.cast_lt.mpr hsmall
    norm_num at hc
    exact hc
  have hbound : factor (x : ℝ) ≤ ⌈1 / x⌉₊ := by
    have hn := (step_bounds (x : ℝ) hxr hsr).2.2.2.1
    have ha : (factor (x : ℝ) : ℝ) ≤ 1 / (x : ℝ) := by
      apply (le_div_iff₀ hxr).mpr
      change next (x : ℝ) ≤ 1
      linarith
    have hc : (1 : ℝ) / (x : ℝ) ≤ (⌈1 / x⌉₊ : ℝ) := by
      exact_mod_cast (Nat.le_ceil ((1 : ℚ) / x))
    exact_mod_cast ha.trans hc
  have hvalid : 16 * (factor (x : ℝ) : ℚ) ^ 2 * x ≤ 1 := by
    have hr := (factor_integer_comparison (x : ℝ) hxr (factor (x : ℝ))).mp (le_refl _)
    exact_mod_cast hr
  apply le_antisymm
  · have hspec : 16 * (factorRat x : ℚ) ^ 2 * x ≤ 1 :=
      Nat.findGreatest_spec (P := fun a => 16 * (a : ℚ) ^ 2 * x ≤ 1)
        (Nat.zero_le _) (by norm_num)
    apply (factor_integer_comparison (x : ℝ) hxr _).mpr
    exact_mod_cast hspec
  · exact Nat.le_findGreatest hbound hvalid

def ratio (x₀ : ℚ) : ℕ → ℚ
  | 0 => x₀
  | j + 1 => if ratio x₀ j < 1 / 256 then (factorRat (ratio x₀ j) : ℚ) * ratio x₀ j
      else ratio x₀ j

theorem ratio_cast (x₀ : ℚ) (hx : 0 < x₀) (j : ℕ) :
    (ratio x₀ j : ℝ) = rateRatio (x₀ : ℝ) j := by
  have hxr : (0 : ℝ) < x₀ := by exact_mod_cast hx
  induction j with
  | zero => rfl
  | succ j ih =>
      have hp : (0 : ℝ) < ratio x₀ j := by rw [ih]; exact ratio_positive _ hxr j
      have hpq : (0 : ℚ) < ratio x₀ j := by exact_mod_cast hp
      by_cases hc : ratio x₀ j < 1 / 256
      · have hcr : rateRatio (x₀ : ℝ) j < 1 / 256 := by
          rw [← ih]
          have hcast : (ratio x₀ j : ℝ) < ((1 / 256 : ℚ) : ℝ) := Rat.cast_lt.mpr hc
          norm_num at hcast
          exact hcast
        simp only [ratio, if_pos hc, Rat.cast_mul, Rat.cast_natCast,
          rateRatio, if_pos hcr, next]
        rw [factorRat_eq _ hpq hc, ih]
      · have hcr : ¬ rateRatio (x₀ : ℝ) j < 1 / 256 := by
          rw [← ih]
          intro hlt
          apply hc
          apply (Rat.cast_lt (K := ℝ)).mp
          norm_num
          exact hlt
        simp only [ratio, if_neg hc, rateRatio, if_neg hcr, ih]

theorem rational_chain_stops (x₀ : ℚ) (hx : 0 < x₀) (bound : ℕ)
    (hbound : 1 / (64 * x₀) ≤ bound) : 1 / 256 ≤ ratio x₀ (stageCap bound) := by
  have hxr : (0 : ℝ) < x₀ := by exact_mod_cast hx
  have hbr : reciprocal (x₀ : ℝ) ≤ bound := by
    unfold reciprocal
    exact_mod_cast hbound
  have h := stopped_at_double_log (x₀ : ℝ) hxr bound hbr
  rw [← ratio_cast x₀ hx] at h
  apply (Rat.cast_le (K := ℝ)).mp
  norm_num
  exact h

end NearCubicGates.RationalRateChain

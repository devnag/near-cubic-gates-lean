import Proof.Foundations.Semantics

/-!
# Exact asymptotic adapters for the headline boundary

These lemmas isolate the order-sensitive conversions used after canonical
recovery.  They deliberately operate on the concrete headline functions rather
than on an informal `O`-notation layer, so the final proof cannot silently lose
strictness or reverse a cap comparison.
-/

namespace NearCubicWires

theorem logScale_pos (n : ℕ) : 0 < logScale n := by
  exact Nat.clog_pos (by omega) (by omega)

theorem wireScale_mono_coefficient
    {smaller larger : ℝ} (hcoeff : smaller ≤ larger)
    (logExponent n : ℕ) :
    wireScale smaller logExponent n ≤
      wireScale larger logExponent n := by
  unfold wireScale
  gcongr

theorem wireScale_pos
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    (logExponent n : ℕ) (hn : 0 < n) :
    0 < wireScale coefficient logExponent n := by
  unfold wireScale
  have hlog : (0 : ℝ) < logScale n := by
    exact_mod_cast logScale_pos n
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast hn
  positivity

theorem inversePolynomialAdvantage_exponent_reserve
    (n : ℕ) (exponent : ℝ) (hn : 2 ≤ n) :
    inversePolynomialAdvantage n (exponent + 1) <
      inversePolynomialAdvantage n exponent := by
  apply Real.rpow_lt_rpow_of_exponent_lt
  · exact_mod_cast hn
  · linarith

theorem agreement_lt_of_exponent_reserve
    {n : ℕ} {exponent observed : ℝ} (hn : 2 ≤ n)
    (hobserved :
      observed ≤
        1 / 2 + inversePolynomialAdvantage n (exponent + 1)) :
    observed < 1 / 2 + inversePolynomialAdvantage n exponent := by
  have hreserve :=
    inversePolynomialAdvantage_exponent_reserve n exponent hn
  linarith

theorem agreement_lt_of_fixed_reserve
    {observed recovered target : ℝ}
    (hobserved : observed ≤ 1 / 2 + recovered)
    (hreserve : recovered < target) :
    observed < 1 / 2 + target := by
  linarith

end NearCubicWires

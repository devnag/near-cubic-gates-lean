import SourceAdapters.Probability.BernsteinTail

/-!
# Bernstein's inequality for bounded independent random variables

This proves the inequality used in `lem:bernstein` on arbitrary probability
spaces, with almost-everywhere bounds and arbitrary finite index sets. Its
specialization proves the full statement of Vershynin's Theorem 2.8.4.
-/

set_option autoImplicit false

universe u v

namespace NearCubicGates.Adapters.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The two-sided bounded Bernstein inequality. The variance is the sum of
the exact second moments; the family may be empty. -/
theorem measure_abs_finset_sum_ge_le_bernstein {X : ι → Ω → ℝ} {K t : ℝ}
    (s : Finset ι) (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (hK : 0 ≤ K) (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
      2 * Real.exp (-(t ^ 2) / (2 * ((∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) + K * t / 3))) := by
  have hp := measure_finset_sum_ge_le_bernstein s hX hind hK hbound hmean ht
  have hnegind : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hn := measure_finset_sum_ge_le_bernstein (X := fun i ω => -X i ω) s
    (fun i => (hX i).neg) hnegind hK
    (fun i hi => by simpa only [abs_neg] using hbound i hi)
    (fun i hi => by simp only [integral_neg, hmean i hi, neg_zero]) ht
  simp only [Finset.sum_neg_distrib, neg_sq] at hn
  have hevent : {ω | t ≤ |∑ i ∈ s, X i ω|} =
      {ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -(∑ i ∈ s, X i ω)} := by
    ext ω
    change t ≤ |∑ i ∈ s, X i ω| ↔ t ≤ ∑ i ∈ s, X i ω ∨ t ≤ -(∑ i ∈ s, X i ω)
    exact le_abs
  rw [hevent]
  have hu := measureReal_union_le (μ := μ)
    {ω | t ≤ ∑ i ∈ s, X i ω} {ω | t ≤ -(∑ i ∈ s, X i ω)}
  linarith

/-- Bernstein's inequality indexed by any finite type. -/
theorem measure_abs_sum_ge_le_bernstein [Fintype ι] {X : ι → Ω → ℝ} {K t : ℝ}
    (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2) / (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + K * t / 3))) :=
  measure_abs_finset_sum_ge_le_bernstein Finset.univ hX hind hK
    (fun i _ => hbound i) (fun i _ => hmean i) ht

end NearCubicGates.Adapters.Probability

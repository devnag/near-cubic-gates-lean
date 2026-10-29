import SourceAdapters.Probability.BernsteinMGF

/-!
# The one-sided bounded Bernstein inequality

For `lem:bernstein`, apply the Chernoff bound at the variance-sensitive
parameter `t / (V + K*t/3)`. Zero variance is treated by almost-everywhere
vanishing, without dividing by the variance.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A finite sum of uniformly bounded variables is bounded almost everywhere. -/
theorem abs_finset_sum_le {X : ι → Ω → ℝ} {K : ℝ} (s : Finset ι)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ K) :
    ∀ᵐ ω ∂μ, |∑ i ∈ s, X i ω| ≤ s.card * K := by
  filter_upwards [(s.eventually_all).mpr hbound] with ω hω
  calc
    |∑ i ∈ s, X i ω| ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, K := Finset.sum_le_sum hω
    _ = s.card * K := by simp

/-- A vanishing sum of second moments forces every term, hence the sum, to
vanish almost everywhere. Independence is not needed. -/
theorem finset_sum_ae_zero_of_secondMoment_sum_zero {X : ι → Ω → ℝ} {K : ℝ}
    (s : Finset ι) (hX : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hzero : (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) = 0) :
    (fun ω => ∑ i ∈ s, X i ω) =ᵐ[μ] 0 := by
  have hv : ∀ i ∈ s, (∫ ω, (X i ω) ^ 2 ∂μ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => integral_nonneg fun ω => sq_nonneg (X i ω))).mp hzero
  have hz : ∀ i ∈ s, X i =ᵐ[μ] 0 := by
    intro i hi
    have hh := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X i ω))
      (integrable_sq_of_abs_le (hX i) (hbound i hi))).mp (hv i hi)
    filter_upwards [hh] with ω hω
    exact sq_eq_zero_iff.mp hω
  filter_upwards [(s.eventually_all).mpr hz] with ω hω
  exact Finset.sum_eq_zero hω

/-- Algebra of the Chernoff parameter when the variance is positive. -/
theorem bernstein_optimizer (V K t : ℝ) (hV : 0 < V) (hK : 0 ≤ K) (ht : 0 ≤ t) :
    let r := t / (V + K * t / 3)
    0 ≤ r ∧ r * K < 3 ∧
      -r * t + r ^ 2 * V / (2 * (1 - r * K / 3)) = -(t ^ 2) / (2 * (V + K * t / 3)) := by
  let D := V + K * t / 3
  have hD : 0 < D := by dsimp [D]; positivity
  have hcut : t / D * K < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    dsimp [D]
    nlinarith
  refine ⟨div_nonneg ht hD.le, hcut, ?_⟩
  change -(t / D) * t + (t / D) ^ 2 * V / (2 * (1 - t / D * K / 3)) = -(t ^ 2) / (2 * D)
  have he : 1 - t / D * K / 3 = V / D := by
    field_simp
    dsimp [D]
    ring
  rw [he]
  field_simp
  ring

/-- Bernstein's upper-tail bound for a finite independent family of centered,
almost-everywhere bounded real random variables. -/
theorem measure_finset_sum_ge_le_bernstein {X : ι → Ω → ℝ} {K t : ℝ}
    (s : Finset ι) (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (hK : 0 ≤ K) (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-(t ^ 2) / (2 * ((∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) + K * t / 3))) := by
  let V := ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg (X i ω)
  rcases ht.eq_or_lt with rfl | htpos
  · simp
  by_cases hz : V = 0
  · have hs := finset_sum_ae_zero_of_secondMoment_sum_zero s hX hbound hz
    have he : {ω | t ≤ ∑ i ∈ s, X i ω} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hs] with ω hω
      change (t ≤ ∑ i ∈ s, X i ω) = False
      simp only [hω, Pi.zero_apply, htpos.not_ge, eq_self]
    rw [measureReal_congr he, measureReal_empty]
    exact (Real.exp_pos _).le
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
  let r := t / (V + K * t / 3)
  obtain ⟨hr, hrK, heq⟩ := bernstein_optimizer V K t hVpos hK htpos.le
  have hmgf := mgf_finset_sum_le_bernstein s hX hind hK hbound hmean hr hrK
  have hfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    funext ω
    exact (Finset.sum_apply ω s X).symm
  have hsummeas : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) μ := by
    rw [hfun]
    exact s.aemeasurable_sum (fun i _ => hX i)
  have hsi : Integrable (fun ω => Real.exp (r * (∑ i ∈ s, X i ω))) μ :=
    integrable_exp_mul_of_mem_Icc hsummeas (by
      filter_upwards [abs_finset_sum_le s hbound] with ω hω
      exact abs_le.mp hω)
  have hc := measure_ge_le_exp_mul_mgf t hr hsi
  calc
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
        Real.exp (-r * t) * mgf (fun ω => ∑ i ∈ s, X i ω) μ r := hc
    _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * V / (2 * (1 - r * K / 3))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [hfun]
      exact hmgf
    _ = Real.exp (-(t ^ 2) / (2 * (V + K * t / 3))) := by
      rw [← Real.exp_add, heq]

end NearCubicGates.Adapters.Probability

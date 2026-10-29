import SourceAdapters.Probability.BernsteinExp
import Mathlib.Probability.Moments.Basic

/-!
# Variance-sensitive moment-generating-function bounds

For `lem:bernstein`, integrate the quadratic exponential estimate. The linear
term vanishes by centering; independence then turns the finite-sum MGF into a
product. Bounds are almost everywhere, on an arbitrary probability space.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An almost-everywhere bounded real random variable is integrable. -/
theorem integrable_of_abs_le {X : Ω → ℝ} {K : ℝ} (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K) : Integrable X μ := by
  apply Integrable.of_mem_Icc (-K) K hX
  filter_upwards [hbound] with ω hω
  exact abs_le.mp hω

/-- Its second moment is also integrable. -/
theorem integrable_sq_of_abs_le {X : Ω → ℝ} {K : ℝ} (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K) :
    Integrable (fun ω => (X ω) ^ 2) μ := by
  apply Integrable.of_mem_Icc 0 (K ^ 2) (hX.pow_const 2)
  filter_upwards [hbound] with ω hω
  refine ⟨sq_nonneg _, ?_⟩
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (X ω)) hω 2

/-- The one-variable Bernstein MGF bound, with the exact second moment. -/
theorem mgf_le_bernstein {X : Ω → ℝ} {K r : ℝ} (hX : AEMeasurable X μ)
    (hK : 0 ≤ K) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K) (hmean : ∫ ω, X ω ∂μ = 0)
    (hr : 0 ≤ r) (hrK : r * K < 3) :
    mgf X μ r ≤ Real.exp (r ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) / (2 * (1 - r * K / 3))) := by
  let c := r ^ 2 / (2 * (1 - r * K / 3))
  have hXi := integrable_of_abs_le hX hbound
  have hXi2 := integrable_sq_of_abs_le hX hbound
  have hei : Integrable (fun ω => Real.exp (r * X ω)) μ :=
    integrable_exp_mul_of_mem_Icc hX (by
      filter_upwards [hbound] with ω hω
      exact abs_le.mp hω)
  have hupper : Integrable (fun ω => 1 + r * X ω + c * (X ω) ^ 2) μ :=
    ((integrable_const 1).add (hXi.const_mul r)).add (hXi2.const_mul c)
  have hpoint : (fun ω => Real.exp (r * X ω)) ≤ᵐ[μ]
      (fun ω => 1 + r * X ω + c * (X ω) ^ 2) := by
    filter_upwards [hbound] with ω hω
    have hb : |r * X ω| ≤ r * K := by
      rw [abs_mul, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_left hω hr
    have h := exp_le_one_add_add_quadratic (r * X ω) (r * K)
      (mul_nonneg hr hK) hrK hb
    convert h using 1
    dsimp [c]
    ring
  have hi := integral_mono_ae hei hupper hpoint
  have hm : mgf X μ r ≤ 1 + c * (∫ ω, (X ω) ^ 2 ∂μ) := by
    have hlin : Integrable (fun ω => 1 + r * X ω) μ :=
      (integrable_const 1).add (hXi.const_mul r)
    rw [integral_add (f := fun ω => 1 + r * X ω) (g := fun ω => c * (X ω) ^ 2)
      hlin (hXi2.const_mul c),
      integral_add (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => r * X ω)
        (integrable_const 1) (hXi.const_mul r), integral_const_mul,
      integral_const_mul, hmean] at hi
    simpa only [mgf, integral_const, probReal_univ, smul_eq_mul, one_mul,
      mul_zero, add_zero] using hi
  calc
    mgf X μ r ≤ 1 + c * (∫ ω, (X ω) ^ 2 ∂μ) := hm
    _ ≤ Real.exp (c * (∫ ω, (X ω) ^ 2 ∂μ)) := by
      simpa only [add_comm] using Real.add_one_le_exp (c * (∫ ω, (X ω) ^ 2 ∂μ))
    _ = Real.exp (r ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) / (2 * (1 - r * K / 3))) := by
      congr 1
      dsimp [c]
      ring

/-- Independence adds second moments in the Bernstein MGF estimate. -/
theorem mgf_finset_sum_le_bernstein {X : ι → Ω → ℝ} {K r : ℝ}
    (s : Finset ι) (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (hK : 0 ≤ K) (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) (hr : 0 ≤ r) (hrK : r * K < 3) :
    mgf (∑ i ∈ s, X i) μ r ≤
      Real.exp (r ^ 2 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) / (2 * (1 - r * K / 3))) := by
  rw [hind.mgf_sum₀ hX s]
  calc
    ∏ i ∈ s, mgf (X i) μ r ≤
        ∏ i ∈ s, Real.exp (r ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / (2 * (1 - r * K / 3))) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        exact mgf_le_bernstein (hX i) hK (hbound i hi) (hmean i hi) hr hrK
    _ = Real.exp (r ^ 2 * (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) / (2 * (1 - r * K / 3))) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, Finset.sum_div]

end NearCubicGates.Adapters.Probability

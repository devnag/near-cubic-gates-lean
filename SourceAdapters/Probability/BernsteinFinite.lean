import SourceAdapters.Probability.Bernstein
import NineInputs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bernstein's inequality for finite uniform samples

The inequality of `lem:bernstein` is stated in the released interface using
finite uniform averages. The uniform-measure conversion below is adapted from
`SourceAdapters/Base/Bernstein.lean`; it now applies the native finite-family
Bernstein theorem directly, without a published-result assumption or reindexing.
-/

set_option autoImplicit false

universe u v

namespace NearCubicGates.Adapters.Probability

open MeasureTheory ProbabilityTheory
open NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness

section Uniform

variable (Ω : Type u) [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

/-- The uniform probability measure on a finite nonempty sample type. -/
noncomputable def uniformMeasure : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure

instance uniformMeasure.isProbabilityMeasure : IsProbabilityMeasure (uniformMeasure Ω) := by
  unfold uniformMeasure
  infer_instance

variable {Ω}

theorem mean_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ mean f := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  unfold indicator
  split_ifs <;> norm_num

/-- Integration against the uniform measure equals the finite average. -/
theorem integral_uniformMeasure (f : Ω → ℝ) : ∫ ω, f ω ∂uniformMeasure Ω = mean f := by
  unfold uniformMeasure mean
  rw [PMF.integral_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [PMF.uniformOfFintype_apply, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_inv_mul]

/-- Uniform event probabilities are averages of their indicators. -/
theorem measureReal_uniformMeasure (A : Set Ω) :
    (uniformMeasure Ω).real A = mean (fun ω => indicator (ω ∈ A)) := by
  rw [← integral_indicator_one (MeasurableSet.of_discrete (s := A)), integral_uniformMeasure]
  congr 1

theorem measure_uniformMeasure (A : Set Ω) :
    uniformMeasure Ω A = ENNReal.ofReal (mean (fun ω => indicator (ω ∈ A))) := by
  rw [← measureReal_uniformMeasure, ofReal_measureReal]

/-- Factorization of finite uniform event averages gives measure-theoretic
mutual independence. -/
theorem iIndepFun_of_finiteIndependent {ι : Type v} (Y : ι → Ω → ℝ) (h : finiteIndependent Y) :
    iIndepFun Y (uniformMeasure Ω) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  rw [measure_uniformMeasure]
  simp_rw [measure_uniformMeasure]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => mean_nonneg fun ω => indicator_nonneg _]
  congr 1
  have key := h S sets
  simp only [Set.mem_iInter, Set.mem_preimage]
  exact key

end Uniform

/-- The finite-uniform Bernstein inequality at arbitrary sample and index
universes, proved directly from the native probability-space theorem. -/
theorem finiteBernstein_universe :
    Vershynin18_Theorem2_8_4_FiniteBernstein.{u, v} := by
  unfold Vershynin18_Theorem2_8_4_FiniteBernstein
  intro Samples Terms _ _ _ _ Y hind hmean hbound s hs
  letI : MeasurableSpace Samples := ⊤
  haveI : DiscreteMeasurableSpace Samples := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hmean' : ∀ i, ∫ ω, Y i ω ∂uniformMeasure Samples = 0 := by
    intro i
    rw [integral_uniformMeasure]
    exact hmean i
  have h := measure_abs_sum_ge_le_bernstein (μ := uniformMeasure Samples)
    (fun _ => Measurable.of_discrete.aemeasurable) (iIndepFun_of_finiteIndependent Y hind)
    (by norm_num : (0 : ℝ) ≤ 1) (fun i => Filter.Eventually.of_forall (hbound i)) hmean' hs.le
  simpa only [measureReal_uniformMeasure, integral_uniformMeasure, Set.mem_setOf_eq, one_mul] using h

/-- The exact released Bernstein field, with no source-result hypothesis. -/
theorem finiteBernstein : Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0} :=
  finiteBernstein_universe.{0, 0}

end NearCubicGates.Adapters.Probability

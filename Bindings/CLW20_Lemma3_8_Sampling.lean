import Proof.Foundations.RepresentationSourceContracts

/-! # CLW20 Lemma 3.8, Appendix A: the sampling step

CLW20 (ECCC TR20-150), Appendix A, PDF p.50–51, printed pp.49–50, Case 2:

> "Now let Z_1, Z_2, ..., Z_ℓ be a sequence of i.i.d. random variables, where each Z_i is uniformly
> random from {0,1}^{n(k−1)}. [...] Setting ℓ = O(n/(δε_k)^2), and applying a Chernoff bound, we
> have Pr_{Z_i}[|T(y) − T̃(y)| ≥ δε_k/(2(1 − δ))] ≤ 2^{−n−1}. By a union bound, we can fix an
> assignment Z_i = z_i for each of Z_i such that |T(y) − T̃(y)| ≤ δε_k/(2(1 − δ)) (27) holds, for
> all y ∈ {0,1}^n."

This module proves that step without any probability in its statement
(`exists_sample_at_level`): for the sample count `sampleCount δ n j = ⌈4(n+1)/(δ²ε_j²)⌉` fixed by
the imported `SampleForm`, one choice of the `ℓ` samples makes every empirical mean within
`δε_j/(2(1−δ))` of its exact mean, simultaneously for all `2^n` inputs `y`.

Reading recorded here: the printed `O(n/(δε_k)^2)` is instantiated at the explicit count
`⌈4(n+1)/(δ²ε_k²)⌉`, and the printed "Chernoff bound" is Hoeffding's inequality for {0,1}-valued
samples (Mathlib `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` with Hoeffding's lemma
`hasSubgaussianMGF_of_mem_Icc`). The failure probability obtained per input is
`2·exp(−2(n+1)/(1−δ)²)` rather than the printed `2^{−n−1}`; either suffices for the union bound
over `2^n` inputs, which is all the proof uses. The two arithmetic lemmas are `sample_exponent_bound`
and `union_budget_lt_one`. -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces RepairRepresentation
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bitAsReal_not (b : Bool) : bitAsReal (!b) = 1 - bitAsReal b := by
  cases b <;> simp [bitAsReal]

/-- The exact finite mean of a Boolean predicate (the paper's `Pr_z[...]`). -/
noncomputable def mean {α : Type*} [Fintype α] (g : α → Bool) : ℝ :=
  (∑ a, bitAsReal (g a)) / (Fintype.card α : ℝ)

theorem mean_not {α : Type*} [Fintype α] [Nonempty α] (g : α → Bool) :
    mean (fun a => !g a) = 1 - mean g := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mean, bitAsReal_not, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  field_simp

section Tail
variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The uniform probability measure on a finite type ("uniformly random"). -/
noncomputable def unif (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance unif_isProbability : IsProbabilityMeasure (unif α) := by
  unfold unif
  infer_instance

theorem integral_unif (g : α → Bool) : ∫ a, bitAsReal (g a) ∂(unif α) = mean g := by
  rw [unif, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, mean]
  rw [← Finset.mul_sum, inv_mul_eq_div]

/-- Hoeffding's inequality for `ℓ` i.i.d. uniform samples of a {0,1}-valued predicate. -/
theorem upper_tail (ell : ℕ) (g : α → Bool) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin ell => unif α).real
      {ω | t ≤ ∑ i, (bitAsReal (g (ω i)) - mean g)} ≤ Real.exp (-(2 * t ^ 2) / ell) := by
  set μ := Measure.pi fun _ : Fin ell => unif α
  have hindep : iIndepFun (fun (i : Fin ell) (ω : Fin ell → α) => bitAsReal (g (ω i)) - mean g) μ :=
    iIndepFun_pi (X := fun _ a => bitAsReal (g a) - mean g)
      (fun _ => (Measurable.of_discrete).aemeasurable)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin ell)),
      HasSubgaussianMGF (fun ω : Fin ell → α => bitAsReal (g (ω i)) - mean g)
        ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i _
    have hm : AEMeasurable (fun ω : Fin ell → α => bitAsReal (g (ω i))) μ :=
      ((Measurable.of_discrete (f := fun a : α => bitAsReal (g a))).comp
        (measurable_pi_apply i)).aemeasurable
    have hb : ∀ᵐ ω ∂μ, bitAsReal (g (ω i)) ∈ Set.Icc (0 : ℝ) 1 :=
      Filter.Eventually.of_forall fun ω => by cases g (ω i) <;> simp [bitAsReal]
    have h := hasSubgaussianMGF_of_mem_Icc hm hb
    have hmean : μ[fun ω : Fin ell → α => bitAsReal (g (ω i))] = mean g := by
      rw [integral_comp_eval (μ := fun _ : Fin ell => unif α) (i := i)
        (f := fun a => bitAsReal (g a)) Measurable.of_discrete.aestronglyMeasurable]
      exact integral_unif g
    rw [hmean] at h
    exact h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep hsub ht
  refine le_of_le_of_eq h ?_
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

end Tail

/-- The union bound: if the budget is below one, some sample sequence is simultaneously accurate
at every index `y`. No probability appears in the statement. -/
theorem exists_accurate_sample {Y α : Type*} [Fintype Y] [Fintype α] [Nonempty α]
    (ell : ℕ) (hell : 0 < ell) (g : Y → α → Bool) (tau : ℝ) (htau : 0 < tau)
    (hunion : (Fintype.card Y : ℝ) * (2 * Real.exp (-(2 * ell * tau ^ 2))) < 1) :
    ∃ zs : Fin ell → α, ∀ y,
      |(∑ i, bitAsReal (g y (zs i))) / ell - mean (g y)| ≤ tau := by
  letI : MeasurableSpace α := ⊤
  set μ := Measure.pi fun _ : Fin ell => unif α
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell
  let up : Y → Set (Fin ell → α) := fun y =>
    {ω | ell * tau ≤ ∑ i, (bitAsReal (g y (ω i)) - mean (g y))}
  let down : Y → Set (Fin ell → α) := fun y =>
    {ω | ell * tau ≤ ∑ i, (bitAsReal ((fun a => !g y a) (ω i)) - mean (fun a => !g y a))}
  have hexp : Real.exp (-(2 * (ell * tau) ^ 2) / ell) = Real.exp (-(2 * ell * tau ^ 2)) := by
    congr 1
    field_simp
  have hone : ∀ y, μ.real (up y ∪ down y) ≤ 2 * Real.exp (-(2 * ell * tau ^ 2)) := by
    intro y
    have h1 := upper_tail ell (g y) (ell * tau) (by positivity)
    have h2 := upper_tail ell (fun a => !g y a) (ell * tau) (by positivity)
    rw [hexp] at h1 h2
    calc μ.real (up y ∪ down y) ≤ μ.real (up y) + μ.real (down y) := measureReal_union_le _ _
      _ ≤ _ := by linarith
  have hbad : μ.real (⋃ y, (up y ∪ down y)) < 1 := by
    calc μ.real (⋃ y, (up y ∪ down y)) ≤ ∑ y, μ.real (up y ∪ down y) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ _y : Y, 2 * Real.exp (-(2 * ell * tau ^ 2)) := Finset.sum_le_sum fun y _ => hone y
      _ = (Fintype.card Y : ℝ) * (2 * Real.exp (-(2 * ell * tau ^ 2))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < 1 := hunion
  have hne : (⋃ y, (up y ∪ down y)) ≠ Set.univ := by
    intro h
    rw [h, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  obtain ⟨zs, hzs⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨zs, fun y => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_union, not_exists, not_or] at hzs
  obtain ⟨hu, hd⟩ := hzs y
  simp only [up, down, Set.mem_setOf_eq, not_le] at hu hd
  simp only [bitAsReal_not, mean_not] at hd
  rw [Finset.sum_sub_distrib] at hu hd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hu hd
  rw [Finset.sum_sub_distrib] at hd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hd
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hell']
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hell']
    nlinarith

theorem xorEpsilon_pos {delta : ℝ} (h1 : delta < 1 / 2) (j : ℕ) :
    0 < xorEpsilon delta j := by
  unfold xorEpsilon
  have ha : 0 < 1 - delta := by linarith
  have hb : 0 < 1 / 2 - delta := by linarith
  positivity

/-- The imported count pays the Hoeffding exponent `2(n+1)/(1−δ)²` at the printed tolerance
`δε_j/(2(1−δ))`. -/
theorem sample_exponent_bound (delta : ℚ) (h0 : 0 < delta) (h1 : delta < 1 / 2) (n j : ℕ) :
    2 * ((n + 1 : ℕ) : ℝ) / (1 - (delta : ℝ)) ^ 2 ≤
      2 * (sampleCount delta n j : ℝ) *
        ((delta : ℝ) * xorEpsilon (delta : ℝ) j / (2 * (1 - (delta : ℝ)))) ^ 2 := by
  have hd0 : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast h0
  have hd1 : (delta : ℝ) < 1 / 2 := by
    have h : ((delta : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    simpa using h
  have he : 0 < xorEpsilon (delta : ℝ) j := xorEpsilon_pos hd1 j
  have hq : 0 < 1 - (delta : ℝ) := by linarith
  have hceil : 4 * ((n + 1 : ℕ) : ℝ) / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2) ≤
      (sampleCount delta n j : ℝ) := Nat.le_ceil _
  have hfactor : 0 ≤ ((delta : ℝ) * xorEpsilon (delta : ℝ) j) ^ 2 / (2 * (1 - (delta : ℝ)) ^ 2) := by
    positivity
  have hleft : 2 * ((n + 1 : ℕ) : ℝ) / (1 - (delta : ℝ)) ^ 2 =
      4 * ((n + 1 : ℕ) : ℝ) / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2) *
        (((delta : ℝ) * xorEpsilon (delta : ℝ) j) ^ 2 / (2 * (1 - (delta : ℝ)) ^ 2)) := by
    field_simp
    norm_num
  have hright : 2 * (sampleCount delta n j : ℝ) *
        ((delta : ℝ) * xorEpsilon (delta : ℝ) j / (2 * (1 - (delta : ℝ)))) ^ 2 =
      (sampleCount delta n j : ℝ) *
        (((delta : ℝ) * xorEpsilon (delta : ℝ) j) ^ 2 / (2 * (1 - (delta : ℝ)) ^ 2)) := by
    field_simp
  rw [hleft, hright]
  exact mul_le_mul_of_nonneg_right hceil hfactor

/-- The union bound over the `2^n` inputs is below one. -/
theorem union_budget_lt_one (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1 / 2) (n : ℕ) :
    (2 : ℝ) ^ n * (2 * Real.exp (-(2 * ((n + 1 : ℕ) : ℝ) / (1 - d) ^ 2))) < 1 := by
  have hq : 0 < (1 - d) ^ 2 := by nlinarith
  have hq1 : (1 - d) ^ 2 ≤ 1 := by nlinarith
  have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiv : 2 * ((n + 1 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) / (1 - d) ^ 2 := by
    rw [le_div_iff₀ hq]
    nlinarith
  have hexp : Real.exp (-(2 * ((n + 1 : ℕ) : ℝ) / (1 - d) ^ 2)) ≤
      Real.exp (-(2 * ((n + 1 : ℕ) : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow : Real.exp (-(2 * ((n + 1 : ℕ) : ℝ))) = Real.exp (-2) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hbase : 2 * Real.exp (-2) < 1 := by
    have h3 : (2 : ℝ) + 1 < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
    have hprod : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hpos : 0 < Real.exp (-2) := Real.exp_pos _
    nlinarith
  have hbase0 : 0 ≤ 2 * Real.exp (-2) := by positivity
  calc (2 : ℝ) ^ n * (2 * Real.exp (-(2 * ((n + 1 : ℕ) : ℝ) / (1 - d) ^ 2)))
      ≤ (2 : ℝ) ^ n * (2 * Real.exp (-(2 * ((n + 1 : ℕ) : ℝ)))) := by gcongr
    _ = (2 * Real.exp (-2)) ^ (n + 1) := by
      rw [hpow]
      ring
    _ < 1 := pow_lt_one₀ hbase0 hbase (by omega)

theorem sampleCount_pos (delta : ℚ) (h0 : 0 < delta) (h1 : delta < 1 / 2) (n j : ℕ) :
    0 < sampleCount delta n j := by
  have hd0 : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast h0
  have hd1 : (delta : ℝ) < 1 / 2 := by
    have h : ((delta : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    simpa using h
  have he : 0 < xorEpsilon (delta : ℝ) j := xorEpsilon_pos hd1 j
  unfold sampleCount
  exact Nat.ceil_pos.mpr (by positivity)

theorem card_bitInput (m : ℕ) : (Fintype.card (BitInput m) : ℝ) = 2 ^ m := by
  simp [BitInput]

/-- (27) of Appendix A at level `j`, with the imported sample count: some `ℓ = sampleCount δ n j`
samples make every empirical mean within `δε_j/(2(1−δ))` of the exact mean, for all `y` at once. -/
theorem exists_sample_at_level (delta : ℚ) (h0 : 0 < delta) (h1 : delta < 1 / 2) (n j : ℕ)
    {α : Type*} [Fintype α] [Nonempty α] (g : BitInput n → α → Bool) :
    ∃ zs : Fin (sampleCount delta n j) → α, ∀ y,
      |(∑ i, bitAsReal (g y (zs i))) / (sampleCount delta n j : ℝ) - mean (g y)| ≤
        (delta : ℝ) * xorEpsilon (delta : ℝ) j / (2 * (1 - (delta : ℝ))) := by
  have hd0 : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast h0
  have hd1 : (delta : ℝ) < 1 / 2 := by
    have h : ((delta : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    simpa using h
  have he : 0 < xorEpsilon (delta : ℝ) j := xorEpsilon_pos hd1 j
  have hq : 0 < 1 - (delta : ℝ) := by linarith
  apply exists_accurate_sample (sampleCount delta n j) (sampleCount_pos delta h0 h1 n j) g
    _ (by positivity)
  rw [card_bitInput]
  have hexp := sample_exponent_bound delta h0 h1 n j
  calc (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (sampleCount delta n j : ℝ) *
        ((delta : ℝ) * xorEpsilon (delta : ℝ) j / (2 * (1 - (delta : ℝ)))) ^ 2)))
      ≤ (2 : ℝ) ^ n * (2 * Real.exp (-(2 * ((n + 1 : ℕ) : ℝ) / (1 - (delta : ℝ)) ^ 2))) := by
        gcongr
    _ < 1 := union_budget_lt_one (delta : ℝ) hd0 hd1 n

end NearCubicWires.Bindings.CLW20Lemma38

import Proof.Gates.NestedRateChain

/-! Public rates start from the manuscript's maximum and ceiling, then use
    the actual accelerated recursion. These bounds do not assume that a
    proposed coefficient vector was sampled. -/

set_option autoImplicit false

namespace NearCubicGates.PublicSamplingRates

open NestedRateChain

noncomputable def liveCap (T h ℓ : ℝ) : ℝ := max ℓ (h ^ 2 / (256 * T))
noncomputable def denominator (T h ℓ : ℝ) : ℕ := ⌈4 * liveCap T h ℓ / h⌉₊
noncomputable def targetRate (T h ℓ : ℝ) : ℝ := h ^ 2 / (8 * T * liveCap T h ℓ)
noncomputable def initialRatio (T h ℓ : ℝ) : ℝ :=
  (1 / (denominator T h ℓ : ℝ)) / targetRate T h ℓ
noncomputable def rate (T h ℓ : ℝ) (j : ℕ) : ℝ :=
  targetRate T h ℓ * rateRatio (initialRatio T h ℓ) j

theorem cap_bounds (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) :
    0 < h ∧ ℓ ≤ liveCap T h ℓ ∧ h / 4 ≤ liveCap T h ℓ ∧
      h ^ 2 / (256 * T) ≤ liveCap T h ℓ := by
  have hp : 0 < h := by linarith
  have hc : h ^ 2 / (256 * T) ≤ liveCap T h ℓ := le_max_right _ _
  have hbase : h / 4 ≤ h ^ 2 / (256 * T) := by
    apply (le_div_iff₀ (by positivity : 0 < 256 * T)).mpr
    nlinarith
  exact ⟨hp, le_max_left _ _, hbase.trans hc, hc⟩

theorem denominator_bounds (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) :
    0 < denominator T h ℓ ∧
      4 * liveCap T h ℓ / h ≤ (denominator T h ℓ : ℝ) ∧
      (denominator T h ℓ : ℝ) ≤ 8 * liveCap T h ℓ / h := by
  obtain ⟨hp, _, hc, _⟩ := cap_bounds T h ℓ hT hh
  have hratio : 1 ≤ 4 * liveCap T h ℓ / h := by
    apply (le_div_iff₀ hp).mpr
    linarith
  have hlo : 4 * liveCap T h ℓ / h ≤ (denominator T h ℓ : ℝ) := Nat.le_ceil _
  have hhi : (denominator T h ℓ : ℝ) < 4 * liveCap T h ℓ / h + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hpos : (0 : ℝ) < denominator T h ℓ := by linarith
  refine ⟨by exact_mod_cast hpos, hlo, ?_⟩
  have heq : 8 * liveCap T h ℓ / h = 2 * (4 * liveCap T h ℓ / h) := by ring
  rw [heq]
  linarith

theorem target_bounds (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) :
    0 < targetRate T h ℓ ∧ targetRate T h ℓ ≤ 32 := by
  obtain ⟨hp, _, hc, hb⟩ := cap_bounds T h ℓ hT hh
  have hcap : 0 < liveCap T h ℓ := by linarith
  unfold targetRate
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 8 * T * liveCap T h ℓ)).mpr
  have h := (div_le_iff₀ (by positivity : 0 < 256 * T)).mp hb
  nlinarith

theorem initial_bounds (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) :
    T / h ≤ initialRatio T h ℓ ∧ initialRatio T h ℓ ≤ 2 * T / h ∧
      0 < initialRatio T h ℓ ∧ initialRatio T h ℓ ≤ 1 / 32 := by
  obtain ⟨hp, _, hc, _⟩ := cap_bounds T h ℓ hT hh
  have hcap : 0 < liveCap T h ℓ := by linarith
  obtain ⟨hM, hMl, hMu⟩ := denominator_bounds T h ℓ hT hh
  have hMr : (0 : ℝ) < denominator T h ℓ := by exact_mod_cast hM
  have hstar := (target_bounds T h ℓ hT hh).1
  have hmlo : 4 * liveCap T h ℓ ≤ (denominator T h ℓ : ℝ) * h :=
    (div_le_iff₀ hp).mp hMl
  have hmhi : (denominator T h ℓ : ℝ) * h ≤ 8 * liveCap T h ℓ :=
    (le_div_iff₀ hp).mp hMu
  have heq : initialRatio T h ℓ =
      8 * T * liveCap T h ℓ / ((denominator T h ℓ : ℝ) * h ^ 2) := by
    unfold initialRatio targetRate
    field_simp
  have hlow : T / h ≤ initialRatio T h ℓ := by
    rw [heq]
    apply (div_le_div_iff₀ hp (by positivity : 0 < (denominator T h ℓ : ℝ) * h ^ 2)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hmhi) (mul_nonneg hT.le hp.le)]
  have hu : initialRatio T h ℓ ≤ 2 * T / h := by
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < (denominator T h ℓ : ℝ) * h ^ 2) hp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hmlo) (mul_nonneg hT.le hp.le)]
  refine ⟨hlow, hu, lt_of_lt_of_le (by positivity) hlow, ?_⟩
  apply hu.trans
  apply (div_le_iff₀ hp).mpr
  linarith

theorem all_rates_bounded (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) (j : ℕ) :
    0 < rate T h ℓ j ∧ rate T h ℓ j ≤ 1 := by
  have hi := initial_bounds T h ℓ hT hh
  have hs := target_bounds T h ℓ hT hh
  have hx := ratio_positive _ hi.2.2.1 j
  have hu := ratio_upper _ hi.2.2.1 hi.2.2.2 j
  unfold rate
  refine ⟨mul_pos hs.1 hx, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hx.le,
    mul_nonneg (sub_nonneg.mpr hu) (by norm_num : (0 : ℝ) ≤ 32)]

theorem rate_is_rational_product (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) (j : ℕ) :
    rate T h ℓ j = (product (initialRatio T h ℓ) j : ℝ) / denominator T h ℓ := by
  have hs := (target_bounds T h ℓ hT hh).1
  unfold rate
  rw [ratio_is_integer_multiple]
  unfold initialRatio
  field_simp

theorem product_fits_denominator (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) (j : ℕ) :
    product (initialRatio T h ℓ) j ≤ denominator T h ℓ := by
  have hprob := (all_rates_bounded T h ℓ hT hh j).2
  rw [rate_is_rational_product T h ℓ hT hh j] at hprob
  have hd : (0 : ℝ) < denominator T h ℓ :=
    by exact_mod_cast (denominator_bounds T h ℓ hT hh).1
  have h' := (div_le_iff₀ hd).mp hprob
  exact_mod_cast (by simpa using h' :
    (product (initialRatio T h ℓ) j : ℝ) ≤ (denominator T h ℓ : ℝ))

theorem chain_stops (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) :
    ∃ J : ℕ, J ≤ stageCap ⌈h / T⌉₊ ∧
      1 / 256 ≤ rateRatio (initialRatio T h ℓ) J ∧
      ∀ j, j < J → rateRatio (initialRatio T h ℓ) j < 1 / 256 := by
  have hi := initial_bounds T h ℓ hT hh
  have hp := (cap_bounds T h ℓ hT hh).1
  have hx0 : 0 < initialRatio T h ℓ := hi.2.2.1
  have hb : reciprocal (initialRatio T h ℓ) ≤ ⌈h / T⌉₊ := by
    apply le_trans _ (Nat.le_ceil (h / T))
    unfold reciprocal
    apply (div_le_div_iff₀ (by positivity : 0 < 64 * initialRatio T h ℓ) hT).mpr
    have hbase := (div_le_iff₀ hp).mp hi.1
    nlinarith
  exact ⟨stoppingIndex _ hi.2.2.1 _ hb,
    stoppingIndex_spec _ hi.2.2.1 _ hb⟩

theorem chain_length_guard (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (n : ℕ) (hsize : h / T ≤ n) :
    ∃ J : ℕ, J + 1 ≤ Nat.clog 2 (Nat.clog 2 n) + 1 ∧
      1 / 256 ≤ rateRatio (initialRatio T h ℓ) J ∧
      ∀ j, j < J → rateRatio (initialRatio T h ℓ) j < 1 / 256 := by
  obtain ⟨J, hJ, hs, ha⟩ := chain_stops T h ℓ hT hh
  have hc : ⌈h / T⌉₊ ≤ n := Nat.ceil_le.mpr hsize
  have hb := stageCap_le_iterated_binary_log _ n hc
  exact ⟨J, by omega, hs, ha⟩

noncomputable def fluctuation (T h ℓ π : ℝ) : ℝ :=
  Real.sqrt (2 * T * π * liveCap T h ℓ) + 2 * T / 3

theorem initial_digit_bound (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) :
    rate T h ℓ 0 * liveCap T h ℓ + fluctuation T h ℓ (rate T h ℓ 0) ≤ h / 2 := by
  have hp := (cap_bounds T h ℓ hT hh).1
  have hcap : 0 < liveCap T h ℓ := by
    have h := (cap_bounds T h ℓ hT hh).2.2.1
    linarith
  have hM := denominator_bounds T h ℓ hT hh
  have hd : (0 : ℝ) < denominator T h ℓ := by exact_mod_cast hM.1
  have hr0 : rate T h ℓ 0 = 1 / denominator T h ℓ := by
    rw [rate_is_rational_product T h ℓ hT hh 0]
    simp [product]
  have hmean : rate T h ℓ 0 * liveCap T h ℓ ≤ h / 4 := by
    rw [hr0]
    rw [one_div_mul_eq_div]
    have hmult := (div_le_iff₀ hp).mp hM.2.1
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hr := (all_rates_bounded T h ℓ hT hh 0).1
  have hv0 : 0 ≤ 2 * T * rate T h ℓ 0 * liveCap T h ℓ := by positivity
  have hv : 2 * T * rate T h ℓ 0 * liveCap T h ℓ ≤ h ^ 2 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmean) (by positivity : 0 ≤ 2 * T)]
  have hs := Real.sq_sqrt hv0
  have hs0 := Real.sqrt_nonneg (2 * T * rate T h ℓ 0 * liveCap T h ℓ)
  have hsbound : Real.sqrt (2 * T * rate T h ℓ 0 * liveCap T h ℓ) ≤ h / 8 := by
    nlinarith
  unfold fluctuation
  linarith

theorem deviation_identity (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h) (j : ℕ) :
    Real.sqrt (2 * T * rate T h ℓ j * liveCap T h ℓ) =
      h / 2 * Real.sqrt (rateRatio (initialRatio T h ℓ) j) := by
  have hp := (cap_bounds T h ℓ hT hh).1
  have hcap : 0 < liveCap T h ℓ := by
    have h := (cap_bounds T h ℓ hT hh).2.2.1
    linarith
  have heq : 2 * T * rate T h ℓ j * liveCap T h ℓ =
      (h / 2) ^ 2 * rateRatio (initialRatio T h ℓ) j := by
    unfold rate targetRate
    field_simp
    ring
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ h / 2)]

theorem correction_digit_bound (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (j : ℕ) (hactive : rateRatio (initialRatio T h ℓ) j < 1 / 256) :
    fluctuation T h ℓ (rate T h ℓ (j + 1)) +
      (factor (rateRatio (initialRatio T h ℓ) j) : ℝ) *
        fluctuation T h ℓ (rate T h ℓ j) ≤ h / 2 := by
  let x := rateRatio (initialRatio T h ℓ) j
  let a : ℝ := factor x
  have hi := initial_bounds T h ℓ hT hh
  have hp := (cap_bounds T h ℓ hT hh).1
  have hx : 0 < x := ratio_positive _ hi.2.2.1 j
  have hs := factor_sqrt_bounds x hx
  have hnext : rateRatio (initialRatio T h ℓ) (j + 1) = next x := by
    simp only [rateRatio, if_pos hactive, x]
  have hn := (step_bounds x hx hactive).2.2.2.1
  have hsn : Real.sqrt (next x) ≤ 1 / 8 := by
    have h := Real.sq_sqrt (step_bounds x hx hactive).2.2.1.le
    have h0 := Real.sqrt_nonneg (next x)
    nlinarith
  have hxbase : T ≤ h * x := by
    have hm : initialRatio T h ℓ ≤ x := ratio_mono _ hi.2.2.1 (Nat.zero_le j)
    have hb := (div_le_iff₀ hp).mp hi.1
    nlinarith
  have ha0 : 0 ≤ a := by positivity
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have ha2 : a ^ 2 * x ≤ 1 / 16 := by
    have hq := factor_integer_comparison x hx (factor x)
    have h := hq.mp (le_refl _)
    dsimp [a]
    linarith
  have haT : a ^ 2 * T ≤ h / 16 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxbase) (sq_nonneg a),
      mul_nonneg (sub_nonneg.mpr ha2) hp.le]
  have haTh : a * T ≤ h / 32 := by
    nlinarith [sq_nonneg (a * T - h / 32),
      mul_nonneg (sub_nonneg.mpr haT) hT.le,
      mul_nonneg (sub_nonneg.mpr hh) hp.le]
  unfold fluctuation
  rw [deviation_identity T h ℓ hT hh (j + 1), deviation_identity T h ℓ hT hh j, hnext]
  change h / 2 * Real.sqrt (next x) + 2 * T / 3 +
    a * (h / 2 * Real.sqrt x + 2 * T / 3) ≤ h / 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hsn) hp.le,
    mul_nonneg (sub_nonneg.mpr hs) hp.le]

theorem terminal_error_bound (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (j : ℕ) (hstopped : 1 / 256 ≤ rateRatio (initialRatio T h ℓ) j) :
    fluctuation T h ℓ (rate T h ℓ j) / rate T h ℓ j ≤ 86 * T * liveCap T h ℓ / h := by
  let x := rateRatio (initialRatio T h ℓ) j
  have hp := (cap_bounds T h ℓ hT hh).1
  have hcap : 0 < liveCap T h ℓ := by
    have hbound := (cap_bounds T h ℓ hT hh).2.2.1
    linarith
  have hr := (all_rates_bounded T h ℓ hT hh j).1
  have hx : 0 < x := ratio_positive _ (initial_bounds T h ℓ hT hh).2.2.1 j
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hs0 := Real.sqrt_nonneg x
  have hslo : 1 / 16 ≤ Real.sqrt x := by nlinarith
  have hsx : Real.sqrt x ≤ 16 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hslo) hs0]
  have hτ : Real.sqrt (2 * T * rate T h ℓ j * liveCap T h ℓ) ≤ 8 * h * x := by
    rw [deviation_identity T h ℓ hT hh j]
    change h / 2 * Real.sqrt x ≤ 8 * h * x
    nlinarith [mul_nonneg (sub_nonneg.mpr hsx) hp.le]
  have hconst : 2 * T / 3 ≤ 11 * h * x / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hstopped) hp.le]
  have heq : (86 * T * liveCap T h ℓ / h) * rate T h ℓ j = 43 * h * x / 4 := by
    unfold rate targetRate
    dsimp [x]
    field_simp
    ring
  apply (div_le_iff₀ hr).mpr
  rw [heq]
  unfold fluctuation
  linarith

theorem certified_public_chain (T h ℓ : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (n : ℕ) (hsize : h / T ≤ n) :
    ∃ J : ℕ,
      J + 1 ≤ Nat.clog 2 (Nat.clog 2 n) + 1 ∧
      (∀ j, 0 < rate T h ℓ j ∧ rate T h ℓ j ≤ 1) ∧
      (∀ j, rate T h ℓ j = (product (initialRatio T h ℓ) j : ℝ) / denominator T h ℓ) ∧
      (∀ j, j < J → 4 ≤ factor (rateRatio (initialRatio T h ℓ) j)) ∧
      rate T h ℓ 0 * liveCap T h ℓ + fluctuation T h ℓ (rate T h ℓ 0) ≤ h / 2 ∧
      (∀ j, j < J → fluctuation T h ℓ (rate T h ℓ (j + 1)) +
        (factor (rateRatio (initialRatio T h ℓ) j) : ℝ) *
          fluctuation T h ℓ (rate T h ℓ j) ≤ h / 2) ∧
      fluctuation T h ℓ (rate T h ℓ J) / rate T h ℓ J ≤ 86 * T * liveCap T h ℓ / h := by
  obtain ⟨J, hJ, hs, ha⟩ := chain_length_guard T h ℓ hT hh n hsize
  refine ⟨J, hJ, all_rates_bounded T h ℓ hT hh,
    rate_is_rational_product T h ℓ hT hh, ?_, initial_digit_bound T h ℓ hT hh,
    fun j hj => correction_digit_bound T h ℓ hT hh j (ha j hj),
    terminal_error_bound T h ℓ hT hh J hs⟩
  intro j hj
  exact (step_bounds _ (ratio_positive _ (initial_bounds T h ℓ hT hh).2.2.1 j) (ha j hj)).1

end NearCubicGates.PublicSamplingRates

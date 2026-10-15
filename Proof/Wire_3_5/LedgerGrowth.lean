import Proof.Wire_3_5.Runtime

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open Filter

def Lq (q : ℕ) : ℕ := Nat.clog 2 (q + 2)

theorem Lq_pos (q : ℕ) : 1 ≤ Lq q := Nat.clog_pos (by norm_num) (by omega)

theorem le_Lq_of_pow_le {q b : ℕ} (h : 2 ^ b ≤ q) : b ≤ Lq q := by
  unfold Lq
  have : b ≤ Nat.log 2 (q + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  exact this.trans (Nat.log_le_clog 2 (q + 2))

theorem tendsto_Lq : Tendsto Lq atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun _ h => le_Lq_of_pow_le h⟩

theorem tendsto_log_Lq : Tendsto (fun q => Nat.log 2 (Lq q)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ?_
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 tendsto_Lq (2 ^ b)
  exact ⟨N, fun q hq => Nat.le_log_of_pow_le (by norm_num) (hN q hq)⟩

/-- `2^{L(q)−1} < q + 2`. -/
theorem two_pow_pred_Lq_lt (q : ℕ) : 2 ^ (Lq q - 1) < q + 2 := by
  have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := q + 2) (by omega)
  simpa [Lq, Nat.pred_eq_sub_one] using this

/-- `L(q) ≤ q + 1`. -/
theorem Lq_le (q : ℕ) : Lq q ≤ q + 1 := by
  unfold Lq
  apply Nat.clog_le_of_le_pow
  have := Nat.lt_two_pow_self (n := q + 1)
  rw [pow_succ]; omega

/-- **Every fixed polynomial is eventually below `2^μ`.** -/
theorem eventually_mul_pow_le_two_pow (K j : ℕ) : ∀ᶠ μ : ℕ in atTop, K * μ ^ j ≤ 2 ^ μ := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt j (by norm_num : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / ((K : ℝ) + 1) by positivity))
  filter_upwards [h] with μ hμ
  have h2 : (0 : ℝ) < 2 ^ μ := by positivity
  rw [div_lt_iff₀ h2] at hμ
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have : (K : ℝ) * (μ : ℝ) ^ j ≤ 2 ^ μ := by
    have h3 : ((K : ℝ) + 1) * (μ : ℝ) ^ j < 2 ^ μ := by
      calc ((K : ℝ) + 1) * (μ : ℝ) ^ j < ((K : ℝ) + 1) * (1 / ((K : ℝ) + 1) * 2 ^ μ) :=
            mul_lt_mul_of_pos_left hμ hK
        _ = 2 ^ μ := by field_simp
    nlinarith [pow_nonneg (Nat.cast_nonneg μ : (0 : ℝ) ≤ μ) j]
  exact_mod_cast this

/-- The affine form: `K·(aμ + b)^j ≤ 2^μ` eventually. -/
theorem eventually_mul_affine_pow_le_two_pow (K a b j : ℕ) :
    ∀ᶠ μ : ℕ in atTop, K * (a * μ + b) ^ j ≤ 2 ^ μ := by
  filter_upwards [eventually_mul_pow_le_two_pow (K * (a + b) ^ j) j, eventually_ge_atTop 1] with μ h hμ
  calc K * (a * μ + b) ^ j ≤ K * ((a + b) * μ) ^ j := by
        apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; nlinarith
    _ = K * (a + b) ^ j * μ ^ j := by rw [mul_pow]; ring
    _ ≤ 2 ^ μ := h

/-- **`C·L(q)^m ≤ q` eventually**: every fixed power of `L` is `o(q)`. -/
theorem eventually_mul_Lq_pow_le (C m : ℕ) : ∀ᶠ q : ℕ in atTop, C * Lq q ^ m ≤ q := by
  have h1 : ∀ᶠ q : ℕ in atTop, 4 * C * (1 * (Lq q - 1) + 1) ^ m ≤ 2 ^ (Lq q - 1) := by
    have hT : Tendsto (fun q => Lq q - 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => by
        obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 tendsto_Lq (b + 1)
        exact ⟨N, fun q hq => by have := hN q hq; omega⟩
    exact hT.eventually (eventually_mul_affine_pow_le_two_pow (4 * C) 1 1 m)
  filter_upwards [h1, eventually_ge_atTop 2] with q h hq
  have hL : 1 * (Lq q - 1) + 1 = Lq q := by have := Lq_pos q; omega
  rw [hL] at h
  have h2 := two_pow_pred_Lq_lt q
  have h4 : 4 * C * Lq q ^ m = 4 * (C * Lq q ^ m) := by ring
  rw [h4] at h
  omega

/-! ## Exact upper integer roots -/

theorem exists_root_ge (j x : ℕ) : ∃ m : ℕ, x ≤ m ^ (j + 1) :=
  ⟨x, by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · exact Nat.zero_le _
    · exact Nat.le_self_pow (Nat.succ_ne_zero j) x⟩

def ceilRoot (j x : ℕ) : ℕ := Nat.find (exists_root_ge j x)

theorem le_ceilRoot_pow (j x : ℕ) : x ≤ ceilRoot j x ^ (j + 1) := Nat.find_spec (exists_root_ge j x)

theorem ceilRoot_min (j x : ℕ) (h : 0 < ceilRoot j x) : (ceilRoot j x - 1) ^ (j + 1) < x := by
  have := Nat.find_min (exists_root_ge j x) (show ceilRoot j x - 1 < ceilRoot j x by omega)
  exact not_le.mp this

/-- `ceilRoot j x ≤ x` for `x ≥ 1`, and `= 0` at `x = 0`. -/
theorem ceilRoot_le_self (j x : ℕ) : ceilRoot j x ≤ x :=
  Nat.find_min' (exists_root_ge j x) (by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · exact Nat.zero_le _
    · exact Nat.le_self_pow (Nat.succ_ne_zero j) x)

theorem ceilRoot_pow_le (j x : ℕ) : ceilRoot j x ^ (j + 1) ≤ 2 ^ (j + 1) * (x + 1) := by
  set m := ceilRoot j x
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m ^ (j + 1) ≤ 1 ^ (j + 1) ∨ m ^ (j + 1) ≤ 2 ^ (j + 1) := by
      right; exact Nat.pow_le_pow_left (by omega) _
    rcases this with h' | h'
    · calc m ^ (j + 1) ≤ 1 := by simpa using h'
        _ ≤ 2 ^ (j + 1) * (x + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    · calc m ^ (j + 1) ≤ 2 ^ (j + 1) := h'
        _ ≤ 2 ^ (j + 1) * (x + 1) := Nat.le_mul_of_pos_right _ (by omega)
  · have hmin := ceilRoot_min j x (by omega)
    have hm : m ≤ 2 * (m - 1) := by omega
    calc m ^ (j + 1) ≤ (2 * (m - 1)) ^ (j + 1) := Nat.pow_le_pow_left hm _
      _ = 2 ^ (j + 1) * (m - 1) ^ (j + 1) := by rw [mul_pow]
      _ ≤ 2 ^ (j + 1) * (x + 1) := Nat.mul_le_mul_left _ (le_of_lt (lt_of_lt_of_le hmin (Nat.le_succ x)))

end NearCubicWires.WireExponent3_5.Ledger

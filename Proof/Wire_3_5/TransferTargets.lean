import Proof.Wire_3_5.LedgerCap
import Proof.Wire_3_5.RowBSchedule
import Proof.Wire_3_5.RowBAsymptotics
import Proof.Wire_3_5.Skeleton

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Ledger (Lq wireCap CapParams capExp32 eventually_mul_Lq_pow_le)
open NearCubicWires.WireExponent3_5.Schedule (eps sched)

/-! ## Elementary facts about `L(q) = ⌈log₂(q+2)⌉` -/

theorem Lq_mono {q n : ℕ} (h : q ≤ n) : Lq q ≤ Lq n := Nat.clog_mono_right 2 (by omega)

theorem two_le_Lq {q : ℕ} (hq : 1 ≤ q) : 2 ≤ Lq q := by
  have : 1 < Nat.clog 2 (q + 2) := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by omega)
  exact this

theorem one_le_Lq (q : ℕ) : 1 ≤ Lq q := Ledger.Lq_pos q

/-- `log₂ L + 1 ≤ (2/log 2)·log L` for `L ≥ 2`. -/
theorem natLog_add_one_le (L : ℕ) (hL : 2 ≤ L) :
    (Nat.log 2 L : ℝ) + 1 ≤ 2 / Real.log 2 * Real.log L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (Nat.log 2 L : ℝ) ≤ Real.log L / Real.log 2 := by
    have := Real.natLog_le_logb L 2
    rw [Real.logb] at this
    exact_mod_cast this
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hL'
  have h3 : 1 ≤ Real.log L / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
  calc (Nat.log 2 L : ℝ) + 1 ≤ Real.log L / Real.log 2 + Real.log L / Real.log 2 := by linarith
    _ = 2 / Real.log 2 * Real.log L := by ring

theorem logFactor_tendsto (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Tendsto (fun q : ℕ => ((Nat.log 2 (Lq q) : ℝ) + 1) ^ a * (Lq q : ℝ) ^ (-b)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS := (Shared.logpow_mul_rpow_neg_tendsto a hb).const_mul ((2 / Real.log 2) ^ a)
  rw [mul_zero] at hS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hS ?_ ?_
  · exact Eventually.of_forall fun q => mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop 1] with q hq
    have hL2 := two_le_Lq hq
    have hbase := natLog_add_one_le (Lq q) hL2
    have hpos : (0 : ℝ) ≤ (Nat.log 2 (Lq q) : ℝ) + 1 := by positivity
    have hlogL : 0 ≤ Real.log (Lq q) := Real.log_nonneg (by exact_mod_cast one_le_Lq q)
    have hpow : ((Nat.log 2 (Lq q) : ℝ) + 1) ^ a ≤ (2 / Real.log 2) ^ a * Real.log (Lq q) ^ a := by
      rw [← Real.mul_rpow (by positivity) hlogL]
      exact Real.rpow_le_rpow hpos hbase ha
    have hLb : (0 : ℝ) ≤ (Lq q : ℝ) ^ (-b) := Real.rpow_nonneg (by positivity) _
    calc ((Nat.log 2 (Lq q) : ℝ) + 1) ^ a * (Lq q : ℝ) ^ (-b)
        ≤ (2 / Real.log 2) ^ a * Real.log (Lq q) ^ a * (Lq q : ℝ) ^ (-b) :=
          mul_le_mul_of_nonneg_right hpow hLb
      _ = (2 / Real.log 2) ^ a * (Real.log (Shared.Lg q) ^ a * ((Shared.Lg q : ℕ) : ℝ) ^ (-b)) := by
          rw [mul_assoc]; rfl

/-- `q^3·√q = q^{7/2}`. -/
theorem pow_three_mul_sqrt (q : ℝ) (hq : 0 ≤ q) : q ^ 3 * Real.sqrt q = q ^ ((7 : ℝ) / 2) := by
  rcases eq_or_lt_of_le hq with h0 | hpos
  · subst h0; simp
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hpos]
  norm_num

theorem cap_eventually (A a : ℝ) (ha : 0 < a) (Kt Kalg : ℝ) (hK : Kalg < Kt) (hKalg : 0 ≤ Kalg) (K₀ : ℕ)
    (qOf : ℕ → ℕ) (hq : Tendsto qOf atTop atTop)
    (hrange : ∀ᶠ n in atTop, qOf n ≤ n ∧ n ≤ K₀ * qOf n * (Nat.log 2 (Lq (qOf n)) + 1)) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ ((7 : ℝ) / 2) / (Lq n : ℝ) ^ Kt ≤
      a * (qOf n : ℝ) ^ ((7 : ℝ) / 2) / (Lq (qOf n) : ℝ) ^ Kalg := by
  set C : ℝ := |A| * (K₀ : ℝ) ^ ((7 : ℝ) / 2) + 1 with hC
  have hC0 : 0 < C := by positivity
  have hlim := (logFactor_tendsto ((7 : ℝ) / 2) (Kt - Kalg) (by norm_num) (by linarith)).comp hq
  have hsmall := hlim.eventually_le_const (u := a / C) (by positivity)
  filter_upwards [hrange, hsmall, hq.eventually_ge_atTop 1] with n hn hs hq1
  obtain ⟨hqn, hnq⟩ := hn
  simp only [Function.comp] at hs
  set q := qOf n
  set Lqq : ℝ := (Lq q : ℝ)
  set ℓ : ℝ := (Nat.log 2 (Lq q) : ℝ) + 1
  have hLqq : (1 : ℝ) ≤ Lqq := by
    show (1 : ℝ) ≤ ((Lq q : ℕ) : ℝ); exact_mod_cast one_le_Lq q
  have hLqq0 : (0 : ℝ) < Lqq := by linarith
  have hLn : Lqq ≤ (Lq n : ℝ) := by
    show ((Lq q : ℕ) : ℝ) ≤ ((Lq n : ℕ) : ℝ); exact_mod_cast Lq_mono hqn
  have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  -- `n^{7/2} ≤ K₀^{7/2} q^{7/2} ℓ^{7/2}`
  have hn72 : (n : ℝ) ^ ((7 : ℝ) / 2) ≤ (K₀ : ℝ) ^ ((7 : ℝ) / 2) * (q : ℝ) ^ ((7 : ℝ) / 2) * ℓ ^ ((7 : ℝ) / 2) := by
    have hle : (n : ℝ) ≤ (K₀ : ℝ) * q * ℓ := by
      have : ((K₀ * q * (Nat.log 2 (Lq q) + 1) : ℕ) : ℝ) = (K₀ : ℝ) * q * ℓ := by push_cast; ring
      rw [← this]; exact_mod_cast hnq
    calc (n : ℝ) ^ ((7 : ℝ) / 2) ≤ ((K₀ : ℝ) * q * ℓ) ^ ((7 : ℝ) / 2) := Real.rpow_le_rpow hn0 hle (by norm_num)
      _ = _ := by rw [Real.mul_rpow (by positivity) hℓ0, Real.mul_rpow (by positivity) hq0]
  -- `L(n)^{Kt} ≥ L(q)^{Kt}`
  have hLpow : Lqq ^ Kt ≤ (Lq n : ℝ) ^ Kt := Real.rpow_le_rpow hLqq0.le hLn (by linarith)
  have hLqKt : 0 < Lqq ^ Kt := Real.rpow_pos_of_pos hLqq0 _
  -- the small factor: `ℓ^{7/2} L(q)^{−(Kt−Kalg)} ≤ a / C`
  have hsplit : Lqq ^ Kt = Lqq ^ (Kt - Kalg) * Lqq ^ Kalg := by
    rw [← Real.rpow_add hLqq0]; ring_nf
  have hneg : Lqq ^ (-(Kt - Kalg)) = (Lqq ^ (Kt - Kalg))⁻¹ := Real.rpow_neg hLqq0.le _
  have hd0 : 0 < Lqq ^ (Kt - Kalg) := Real.rpow_pos_of_pos hLqq0 _
  have hKa0 : 0 < Lqq ^ Kalg := Real.rpow_pos_of_pos hLqq0 _
  have hs' : ℓ ^ ((7 : ℝ) / 2) ≤ a / C * Lqq ^ (Kt - Kalg) := by
    rw [hneg] at hs
    have := mul_le_mul_of_nonneg_right hs hd0.le
    rwa [mul_assoc, inv_mul_cancel₀ hd0.ne', mul_one] at this
  have hK72 : 0 ≤ (K₀ : ℝ) ^ ((7 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq72 : 0 ≤ (q : ℝ) ^ ((7 : ℝ) / 2) := Real.rpow_nonneg hq0 _
  have hℓ72 : 0 ≤ ℓ ^ ((7 : ℝ) / 2) := Real.rpow_nonneg hℓ0 _
  -- assembly
  have hAabs : A ≤ |A| := le_abs_self A
  calc A * (n : ℝ) ^ ((7 : ℝ) / 2) / (Lq n : ℝ) ^ Kt
      ≤ |A| * (n : ℝ) ^ ((7 : ℝ) / 2) / (Lq n : ℝ) ^ Kt := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hAabs (Real.rpow_nonneg hn0 _)
    _ ≤ |A| * (n : ℝ) ^ ((7 : ℝ) / 2) / Lqq ^ Kt :=
        div_le_div_of_nonneg_left (by positivity) hLqKt hLpow
    _ ≤ |A| * ((K₀ : ℝ) ^ ((7 : ℝ) / 2) * (q : ℝ) ^ ((7 : ℝ) / 2) * ℓ ^ ((7 : ℝ) / 2)) / Lqq ^ Kt := by
        apply div_le_div_of_nonneg_right _ hLqKt.le
        exact mul_le_mul_of_nonneg_left hn72 (abs_nonneg _)
    _ ≤ C * (q : ℝ) ^ ((7 : ℝ) / 2) * ℓ ^ ((7 : ℝ) / 2) / Lqq ^ Kt := by
        apply div_le_div_of_nonneg_right _ hLqKt.le
        have : |A| * (K₀ : ℝ) ^ ((7 : ℝ) / 2) ≤ C := by rw [hC]; linarith
        calc |A| * ((K₀ : ℝ) ^ ((7 : ℝ) / 2) * (q : ℝ) ^ ((7 : ℝ) / 2) * ℓ ^ ((7 : ℝ) / 2))
            = (|A| * (K₀ : ℝ) ^ ((7 : ℝ) / 2)) * ((q : ℝ) ^ ((7 : ℝ) / 2) * ℓ ^ ((7 : ℝ) / 2)) := by ring
          _ ≤ C * ((q : ℝ) ^ ((7 : ℝ) / 2) * ℓ ^ ((7 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_right this (mul_nonneg hq72 hℓ72)
          _ = _ := by ring
    _ ≤ C * (q : ℝ) ^ ((7 : ℝ) / 2) * (a / C * Lqq ^ (Kt - Kalg)) / Lqq ^ Kt := by
        apply div_le_div_of_nonneg_right _ hLqKt.le
        exact mul_le_mul_of_nonneg_left hs' (mul_nonneg hC0.le hq72)
    _ = a * (q : ℝ) ^ ((7 : ℝ) / 2) / Lqq ^ Kalg := by
        rw [hsplit]; field_simp

/-- The length relation gives `n + 2 ≤ (q+2)²` eventually, hence `L(n) ≤ 2 L(q)` (`clog_sq_le`). -/
theorem length_sq_eventually (K₀ : ℕ) (qOf : ℕ → ℕ) (hq : Tendsto qOf atTop atTop)
    (hrange : ∀ᶠ n in atTop, qOf n ≤ n ∧ n ≤ K₀ * qOf n * (Nat.log 2 (Lq (qOf n)) + 1)) :
    ∀ᶠ n in atTop, Lq n ≤ 2 * Lq (qOf n) := by
  filter_upwards [hrange, hq.eventually (eventually_mul_Lq_pow_le K₀ 1)] with n hn hK
  obtain ⟨-, hnq⟩ := hn
  set q := qOf n
  have hlog : Nat.log 2 (Lq q) + 1 ≤ Lq q := Nat.log_lt_self 2 (by have := one_le_Lq q; omega)
  have hKL : K₀ * (Nat.log 2 (Lq q) + 1) ≤ q := by
    rw [pow_one] at hK
    exact (Nat.mul_le_mul_left K₀ hlog).trans hK
  have hn2 : n + 2 ≤ (q + 2) ^ 2 := by
    have : n ≤ q * q := by
      calc n ≤ K₀ * q * (Nat.log 2 (Lq q) + 1) := hnq
        _ = q * (K₀ * (Nat.log 2 (Lq q) + 1)) := by ring
        _ ≤ q * q := Nat.mul_le_mul_left q hKL
    nlinarith
  exact Schedule.clog_sq_le hn2

theorem advantage_eventually (ζ : ℚ) (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (K₀ : ℕ) (qOf : ℕ → ℕ)
    (hq : Tendsto qOf atTop atTop)
    (hrange : ∀ᶠ n in atTop, qOf n ≤ n ∧ n ≤ K₀ * qOf n * (Nat.log 2 (Lq (qOf n)) + 1)) :
    ∀ᶠ n in atTop, xorEpsilon (ζ : ℝ) (sched ζ h0 h1 (Lq (qOf n))) < (Lq n : ℝ) ^ (-((1 : ℝ) / 8)) := by
  have hL : Tendsto (fun n => Lq (qOf n)) atTop atTop := Ledger.tendsto_Lq.comp hq
  filter_upwards [length_sq_eventually K₀ qOf hq hrange, hL.eventually_gt_atTop 4] with n hn2 h4
  have h := Schedule.advantage h0 h1 h4 hn2 (one_le_Lq n)
  have he : (eps ζ (sched ζ h0 h1 (Lq (qOf n))) : ℝ) = xorEpsilon (ζ : ℝ) (sched ζ h0 h1 (Lq (qOf n))) := by
    unfold eps xorEpsilon; push_cast; ring
  rw [← he]; exact h

theorem eps_sched_lower (ζ : ℚ) (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (L : ℕ) (hL : 1 ≤ L) :
    min ((1 / 2 - ζ : ℚ) : ℝ) (((1 - ζ : ℚ) : ℝ) * (L : ℝ) ^ (-((3 : ℝ) / 16))) ≤
      (eps ζ (sched ζ h0 h1 L) : ℝ) := by
  rcases Schedule.sched_min h0 h1 L with h | h
  · rw [h]; refine (min_le_left _ _).trans (le_of_eq ?_)
    unfold eps; push_cast; ring
  · refine (min_le_right _ _).trans ?_
    have he0 : (0 : ℝ) ≤ (eps ζ (sched ζ h0 h1 L) : ℝ) := by exact_mod_cast Schedule.eps_nonneg h0 h1 _
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    have hz : (0 : ℝ) ≤ ((1 - ζ : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ 1 - ζ := by linarith
      exact_mod_cast this
    have h16 : ((1 - ζ : ℚ) : ℝ) ^ 16 < (eps ζ (sched ζ h0 h1 L) : ℝ) ^ 16 * (L : ℝ) ^ 3 := by
      have h' : (((1 - ζ) ^ 16 : ℚ) : ℝ) < ((eps ζ (sched ζ h0 h1 L) ^ 16 * (L : ℚ) ^ 3 : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at h' ⊢
      exact h'
    have hx : 0 ≤ ((1 - ζ : ℚ) : ℝ) * (L : ℝ) ^ (-((3 : ℝ) / 16)) :=
      mul_nonneg hz (Real.rpow_nonneg hL0.le _)
    have key : (((1 - ζ : ℚ) : ℝ) * (L : ℝ) ^ (-((3 : ℝ) / 16))) ^ 16 ≤ (eps ζ (sched ζ h0 h1 L) : ℝ) ^ 16 := by
      rw [mul_pow, ← Real.rpow_natCast ((L : ℝ) ^ (-((3 : ℝ) / 16))) 16, ← Real.rpow_mul hL0.le]
      have hL3 : (L : ℝ) ^ (-((3 : ℝ) / 16) * ((16 : ℕ) : ℝ)) = ((L : ℝ) ^ 3)⁻¹ := by
        rw [show -((3 : ℝ) / 16) * ((16 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hL0.le,
          Real.rpow_natCast]
      rw [hL3]
      have hL3pos : (0 : ℝ) < (L : ℝ) ^ 3 := by positivity
      rw [← div_eq_mul_inv, div_le_iff₀ hL3pos]
      exact h16.le
    exact (pow_le_pow_iff_left₀ hx he0 (by norm_num)).mp key

theorem amplifier_le_eps_eventually (ζ : ℚ) (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (x : ℝ) (hx : 0 < x) :
    ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ (-x) ≤ xorEpsilon (ζ : ℝ) (sched ζ h0 h1 (Lq q)) := by
  have hz0 : (0 : ℝ) < ((1 - ζ : ℚ) : ℝ) := by
    have : (0 : ℚ) < 1 - ζ := by linarith
    exact_mod_cast this
  have he1 : (0 : ℝ) < ((1 / 2 - ζ : ℚ) : ℝ) := by
    have : (0 : ℚ) < 1 / 2 - ζ := by linarith
    exact_mod_cast this
  -- `q^{−x} → 0` and `q^{−x}·L(q)^{3/16} → 0`
  have hq0 : Tendsto (fun q : ℕ => (q : ℝ) ^ (-x)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hx).comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun q : ℕ => (q : ℝ) ^ (-x) * (Lq q : ℝ) ^ ((3 : ℝ) / 16)) atTop (𝓝 0) := by
    -- `L(q) ≤ q + 1 ≤ 2q`, and `(2q)^{3/16} q^{−x} → 0` would need `x > 3/16`; use the logarithm instead:
    -- `L(q) ≤ 2 log₂ q` for `q ≥ 2`, and `(log q)^{3/16} q^{−x} → 0`.
    have hlo := (isLittleO_log_rpow_rpow_atTop ((3 : ℝ) / 16) hx).tendsto_div_nhds_zero
    have hlo' : Tendsto (fun q : ℕ => Real.log q ^ ((3 : ℝ) / 16) / (q : ℝ) ^ x) atTop (𝓝 0) :=
      hlo.comp tendsto_natCast_atTop_atTop
    have hc := hlo'.const_mul ((4 / Real.log 2) ^ ((3 : ℝ) / 16))
    rw [mul_zero] at hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
    · exact Eventually.of_forall fun q => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · filter_upwards [eventually_ge_atTop 2] with q hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      -- `L(q) ≤ log₂(q+2) + 1 ≤ 4 log q / log 2`
      have hLq : (Lq q : ℝ) ≤ 4 / Real.log 2 * Real.log q := by
        have hc1 : Lq q ≤ Nat.log 2 q + 2 := by
          apply Nat.clog_le_of_le_pow
          have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
          calc q + 2 ≤ 2 ^ (Nat.log 2 q + 1) + 2 := by omega
            _ ≤ 2 ^ (Nat.log 2 q + 2) := by
                rw [pow_succ 2 (Nat.log 2 q + 1)]
                have : 2 ≤ 2 ^ (Nat.log 2 q + 1) := Nat.le_self_pow (by omega) 2
                omega
        have hc2 : (Nat.log 2 q : ℝ) ≤ Real.log q / Real.log 2 := by
          have := Real.natLog_le_logb q 2
          rw [Real.logb] at this
          exact_mod_cast this
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
        have h2l : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
        have h1l : 1 ≤ Real.log q / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
        calc (Lq q : ℝ) ≤ (Nat.log 2 q : ℝ) + 2 := by exact_mod_cast hc1
          _ ≤ Real.log q / Real.log 2 + 2 * (Real.log q / Real.log 2) := by linarith
          _ = 3 / Real.log 2 * Real.log q := by ring
          _ ≤ 4 / Real.log 2 * Real.log q := by
              apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by linarith))
              exact div_le_div_of_nonneg_right (by norm_num) hlog2.le
      have hLpow : (Lq q : ℝ) ^ ((3 : ℝ) / 16) ≤ (4 / Real.log 2) ^ ((3 : ℝ) / 16) * Real.log q ^ ((3 : ℝ) / 16) := by
        rw [← Real.mul_rpow (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hLq (by norm_num)
      calc (q : ℝ) ^ (-x) * (Lq q : ℝ) ^ ((3 : ℝ) / 16)
          ≤ (q : ℝ) ^ (-x) * ((4 / Real.log 2) ^ ((3 : ℝ) / 16) * Real.log q ^ ((3 : ℝ) / 16)) :=
            mul_le_mul_of_nonneg_left hLpow (Real.rpow_nonneg hq0.le _)
        _ = (4 / Real.log 2) ^ ((3 : ℝ) / 16) * (Real.log q ^ ((3 : ℝ) / 16) / (q : ℝ) ^ x) := by
            rw [Real.rpow_neg hq0.le]; ring
  -- conclude from the lower bound on `e_{t(q)}`
  have hA := hq0.eventually_le_const (u := ((1 / 2 - ζ : ℚ) : ℝ)) he1
  have hB := hL.eventually_le_const (u := ((1 - ζ : ℚ) : ℝ)) hz0
  filter_upwards [hA, hB, eventually_ge_atTop 1] with q hqa hqb hq1
  have hlow := eps_sched_lower ζ h0 h1 (Lq q) (one_le_Lq q)
  have he : (eps ζ (sched ζ h0 h1 (Lq q)) : ℝ) = xorEpsilon (ζ : ℝ) (sched ζ h0 h1 (Lq q)) := by
    unfold eps xorEpsilon; push_cast; ring
  rw [← he]
  refine le_trans (le_min hqa ?_) hlow
  have hLq0 : (0 : ℝ) < (Lq q : ℝ) := by exact_mod_cast one_le_Lq q
  have hpos : 0 < (Lq q : ℝ) ^ ((3 : ℝ) / 16) := Real.rpow_pos_of_pos hLq0 _
  rw [Real.rpow_neg hLq0.le, ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hqb

/-! ## Plumbing to the consumer's class clauses -/

/-- Native hardness at a cap `w(n)` and advantage `adv(n)`, a target cap below `w(n)` and an advantage below
`L(n)^{−c}`, all eventually, give the `THR∘THR` clause `ThrHardAt c K language A`. -/
theorem thrHardAt_of_eventually (c Kt A : ℝ) (language : Language) (w adv : ℕ → ℝ)
    (native : ∀ᶠ n in atTop, ∀ circuit : ThresholdThresholdCircuit n,
      (circuit.wireCount : ℝ) ≤ w n → agreement circuit.eval (language n) < 1 / 2 + adv n)
    (hcap : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ ((7 : ℝ) / 2) / (Lq n : ℝ) ^ Kt ≤ w n)
    (hadv : ∀ᶠ n : ℕ in atTop, adv n ≤ (Lq n : ℝ) ^ (-c)) : ThrHardAt c Kt language A := by
  obtain ⟨onset, h⟩ := eventually_atTop.mp (native.and (hcap.and hadv))
  refine ⟨onset, fun n hn circuit hwire => ?_⟩
  obtain ⟨hnat, hc, ha⟩ := h n hn
  have := hnat circuit (hwire.trans hc)
  have : adv n ≤ (Nat.clog 2 (n + 2) : ℝ) ^ (-c) := ha
  linarith

/-- The same for the `SYM∘THR` clause `SymHardAt`. -/
theorem symHardAt_of_eventually (c Ks A : ℝ) (language : Language) (w adv : ℕ → ℝ)
    (native : ∀ᶠ n in atTop, ∀ circuit : SymmetricThresholdCircuit n,
      (circuit.wireCount : ℝ) ≤ w n → agreement circuit.eval (language n) < 1 / 2 + adv n)
    (hcap : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ ((7 : ℝ) / 2) / (Lq n : ℝ) ^ Ks ≤ w n)
    (hadv : ∀ᶠ n : ℕ in atTop, adv n ≤ (Lq n : ℝ) ^ (-c)) : SymHardAt c Ks language A := by
  obtain ⟨onset, h⟩ := eventually_atTop.mp (native.and (hcap.and hadv))
  refine ⟨onset, fun n hn circuit hwire => ?_⟩
  obtain ⟨hnat, hc, ha⟩ := h n hn
  have := hnat circuit (hwire.trans hc)
  have : adv n ≤ (Nat.clog 2 (n + 2) : ℝ) ^ (-c) := ha
  linarith

/-- The ledger's native cap is `a·q^{7/2}/L(q)^{K_{m,alg}}`. -/
theorem wireCap_eq (C : CapParams) (m : Mode) (q : ℕ) :
    wireCap C m q = (C.coef m : ℝ) * (q : ℝ) ^ ((7 : ℝ) / 2) / (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) := by
  unfold wireCap
  rw [mul_assoc, pow_three_mul_sqrt _ (Nat.cast_nonneg _)]

theorem rowB_thrHardAt (C : CapParams) (hC : 0 < C.aT) (ζ : ℚ) (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (language : Language)
    (K₀ : ℕ) (qOf : ℕ → ℕ) (hq : Tendsto qOf atTop atTop)
    (hrange : ∀ᶠ n in atTop, qOf n ≤ n ∧ n ≤ K₀ * qOf n * (Nat.log 2 (Lq (qOf n)) + 1)) (adv : ℕ → ℝ)
    (native : ∀ᶠ n in atTop, ∀ circuit : ThresholdThresholdCircuit n,
      (circuit.wireCount : ℝ) ≤ wireCap C .thr (qOf n) → agreement circuit.eval (language n) < 1 / 2 + adv n)
    (hadv : ∀ᶠ n in atTop, adv n ≤ xorEpsilon (ζ : ℝ) (sched ζ h0 h1 (Lq (qOf n)))) :
    ∀ AT : ℝ, 0 < AT → ThrHardAt (1 / 8) (11 / 2) language AT := by
  intro AT _
  refine thrHardAt_of_eventually (1 / 8) (11 / 2) AT language (fun n => wireCap C .thr (qOf n)) adv native ?_ ?_
  · have hcapE := cap_eventually AT (C.coef .thr : ℝ) (by exact_mod_cast hC) (11 / 2) ((capExp32 .thr : ℝ) / 32)
      (by norm_num [capExp32]) (by positivity) K₀ qOf hq hrange
    filter_upwards [hcapE] with n hn
    rw [wireCap_eq]; exact hn
  · filter_upwards [hadv, advantage_eventually ζ h0 h1 K₀ qOf hq hrange] with n ha hb
    have : ((1 : ℝ) / 8) = (1 / 8 : ℝ) := rfl
    exact (ha.trans hb.le)

theorem rowB_symHardAt (C : CapParams) (hC : 0 < C.aS) (ζ : ℚ) (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (language : Language)
    (K₀ : ℕ) (qOf : ℕ → ℕ) (hq : Tendsto qOf atTop atTop)
    (hrange : ∀ᶠ n in atTop, qOf n ≤ n ∧ n ≤ K₀ * qOf n * (Nat.log 2 (Lq (qOf n)) + 1)) (adv : ℕ → ℝ)
    (native : ∀ᶠ n in atTop, ∀ circuit : SymmetricThresholdCircuit n,
      (circuit.wireCount : ℝ) ≤ wireCap C .sym (qOf n) → agreement circuit.eval (language n) < 1 / 2 + adv n)
    (hadv : ∀ᶠ n in atTop, adv n ≤ xorEpsilon (ζ : ℝ) (sched ζ h0 h1 (Lq (qOf n)))) :
    ∀ AS : ℝ, 0 < AS → SymHardAt (1 / 8) (9 / 2) language AS := by
  intro AS _
  refine symHardAt_of_eventually (1 / 8) (9 / 2) AS language (fun n => wireCap C .sym (qOf n)) adv native ?_ ?_
  · have hcapE := cap_eventually AS (C.coef .sym : ℝ) (by exact_mod_cast hC) (9 / 2) ((capExp32 .sym : ℝ) / 32)
      (by norm_num [capExp32]) (by positivity) K₀ qOf hq hrange
    filter_upwards [hcapE] with n hn
    rw [wireCap_eq]; exact hn
  · filter_upwards [hadv, advantage_eventually ζ h0 h1 K₀ qOf hq hrange] with n ha hb
    exact (ha.trans hb.le)

end NearCubicWires.WireExponent3_5.Transfer

import Proof.Wire_3_5.LedgerGrowth

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open Filter

def nativeWidth (kclk Apad N : ℕ) : ℕ :=
  Nat.clog 2 (N ^ (kclk + 2)) + Apad * Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2) + Apad

theorem clog_le_nativeWidth (kclk Apad N : ℕ) : Nat.clog 2 (N ^ (kclk + 2)) ≤ nativeWidth kclk Apad N := by
  unfold nativeWidth; omega

/-- `2^{clog₂ x} ≤ 2x` for `x ≥ 1`. -/
theorem two_pow_clog_le (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases Nat.lt_or_ge x 2 with h | h
  · have : x = 1 := by omega
    subst this; simp
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := x) (by omega)
    rw [Nat.pred_eq_sub_one] at h1
    have h2 : 1 ≤ Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
    have : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by
      rw [show Nat.clog 2 x = (Nat.clog 2 x - 1) + 1 from (Nat.sub_add_cancel h2).symm, pow_succ]
      simp only [Nat.add_sub_cancel]; ring
    omega

theorem nativeWidth_table (kclk Apad N : ℕ) (hN : 1 ≤ N) :
    2 ^ nativeWidth kclk Apad N ≤ (2 * 12 ^ Apad) * N ^ (kclk + 2) * nativeWidth kclk Apad N ^ Apad := by
  set T := N ^ (kclk + 2)
  have hT : 1 ≤ T := Nat.one_le_pow _ _ hN
  set c := Nat.clog 2 T
  set q := nativeWidth kclk Apad N
  have hcq : c ≤ q := clog_le_nativeWidth kclk Apad N
  have h1 : 2 ^ c ≤ 2 * T := two_pow_clog_le T hT
  have h2 : 2 ^ Nat.clog 2 (c + 2) ≤ 2 * (c + 2) := two_pow_clog_le (c + 2) (by omega)
  have hq : q = c + Apad * Nat.clog 2 (c + 2) + Apad := rfl
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · have hA : Apad = 0 := by omega
    rw [hq0, hA]; simp; omega
  have h3 : 2 * (c + 2) ≤ 6 * q := by omega
  calc 2 ^ q = 2 ^ c * (2 ^ Nat.clog 2 (c + 2)) ^ Apad * 2 ^ Apad := by rw [hq, pow_add, pow_add, ← pow_mul, mul_comm Apad]
    _ ≤ (2 * T) * (6 * q) ^ Apad * 2 ^ Apad := by
        gcongr
        exact h2.trans h3
    _ = (2 * 12 ^ Apad) * T * q ^ Apad := by
        rw [mul_pow, show (12 : ℕ) = 6 * 2 by norm_num, mul_pow]; ring

theorem nativeWidth_mono (kclk Apad : ℕ) : Monotone (nativeWidth kclk Apad) := by
  intro N N' h
  unfold nativeWidth
  have h1 : Nat.clog 2 (N ^ (kclk + 2)) ≤ Nat.clog 2 (N' ^ (kclk + 2)) :=
    Nat.clog_mono_right 2 (Nat.pow_le_pow_left h _)
  have h2 := Nat.clog_mono_right 2 (show Nat.clog 2 (N ^ (kclk + 2)) + 2 ≤ Nat.clog 2 (N' ^ (kclk + 2)) + 2 by omega)
  have h3 := Nat.mul_le_mul_left Apad h2
  omega

/-- **The native width grows** (the seed's `TimeBudget.growth`). -/
theorem nativeWidth_growth (kclk Apad : ℕ) :
    ∀ m, ∃ onset, ∀ N, onset ≤ N → m ≤ nativeWidth kclk Apad N := by
  intro m
  refine ⟨2 ^ m, fun N hN => ?_⟩
  have h1 : 2 ^ m ≤ N ^ (kclk + 2) := hN.trans (Nat.le_self_pow (by omega) N |>.trans (le_refl _))
  have h2 : m ≤ Nat.clog 2 (N ^ (kclk + 2)) := by
    have : m ≤ Nat.log 2 (N ^ (kclk + 2)) := Nat.le_log_of_pow_le (by norm_num) h1
    exact this.trans (Nat.log_le_clog 2 _)
  exact h2.trans (clog_le_nativeWidth kclk Apad N)

theorem tendsto_nativeWidth (kclk Apad : ℕ) : Tendsto (nativeWidth kclk Apad) atTop atTop :=
  tendsto_atTop_atTop.2 (nativeWidth_growth kclk Apad)

end NearCubicWires.WireExponent3_5.Ledger

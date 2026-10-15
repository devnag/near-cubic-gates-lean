import Proof.Wire_3_5.RowBSchedule
import Proof.Wire_3_5.LedgerGrowth

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule

variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

def rowBt (q : ℕ) : ℕ := sched ζ h0 h1 (Lq q)

def rowBLambda (CΛ q : ℕ) : ℕ := ⌈(CΛ : ℚ) / eps ζ (rowBt h0 h1 q)⌉₊

def rowBSparse (CΛ Cδ q : ℕ) : ℕ := Cδ * rowBLambda h0 h1 CΛ q ^ 2

/-- `(a+1)^{16} ≤ 2^{16}(a^{16}+1)` for `a ≥ 0`. -/
theorem add_one_pow16_le (a : ℚ) (ha : 0 ≤ a) : (a + 1) ^ 16 ≤ 2 ^ 16 * (a ^ 16 + 1) := by
  rcases le_total a 1 with h | h
  · calc (a + 1) ^ 16 ≤ (1 + 1) ^ 16 := pow_le_pow_left₀ (by linarith) (by linarith) 16
      _ = 2 ^ 16 * 1 := by norm_num
      _ ≤ 2 ^ 16 * (a ^ 16 + 1) := by nlinarith [pow_nonneg ha 16]
  · calc (a + 1) ^ 16 ≤ (a + a) ^ 16 := pow_le_pow_left₀ (by linarith) (by linarith) 16
      _ = 2 ^ 16 * a ^ 16 := by ring
      _ ≤ 2 ^ 16 * (a ^ 16 + 1) := by nlinarith

theorem rowBLambda_pow16_le (CΛ : ℕ) : ∃ K : ℕ, ∀ q, rowBLambda h0 h1 CΛ q ^ 16 ≤ K * Lq q ^ 3 := by
  set K0 : ℚ := 2 ^ 16 * (((CΛ : ℚ) / (1 / 2 - ζ)) ^ 16 + (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 + 1)
  refine ⟨⌈K0⌉₊, fun q => ?_⟩
  set t := rowBt h0 h1 q
  set e := eps ζ t
  have he : 0 < e := eps_pos h0 h1 t
  have hL : (1 : ℚ) ≤ Lq q := by exact_mod_cast Lq_pos q
  have hL3 : (1 : ℚ) ≤ (Lq q : ℚ) ^ 3 := one_le_pow₀ hL
  set a : ℚ := (CΛ : ℚ) / e
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) he.le
  have hceil : (rowBLambda h0 h1 CΛ q : ℚ) ≤ a + 1 := (Nat.ceil_lt_add_one ha).le
  have hpow : (rowBLambda h0 h1 CΛ q : ℚ) ^ 16 ≤ 2 ^ 16 * (a ^ 16 + 1) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 16).trans (add_one_pow16_le a ha)
  -- a^16 ≤ (C/(1/2−ζ))^16 + C^16 L^3/(1−ζ)^16
  have ha16 : a ^ 16 ≤ ((CΛ : ℚ) / (1 / 2 - ζ)) ^ 16 + (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (Lq q : ℚ) ^ 3 := by
    rcases sched_min h0 h1 (Lq q) with ht | ht
    · have het : e = 1 / 2 - ζ := by simp only [e, t, rowBt, ht, eps]; simp
      have : a = (CΛ : ℚ) / (1 / 2 - ζ) := by simp only [a, het]
      rw [this]
      have : (0 : ℚ) ≤ (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (Lq q : ℚ) ^ 3 := by positivity
      linarith
    · have h1ζ : (0 : ℚ) < (1 - ζ) ^ 16 := pow_pos (by linarith) _
      have hkey : a ^ 16 ≤ (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (Lq q : ℚ) ^ 3 := by
        have he16 : 0 < e ^ 16 := pow_pos he 16
        have : a ^ 16 = (CΛ : ℚ) ^ 16 / e ^ 16 := by simp only [a, div_pow]
        rw [this, div_le_iff₀ he16]
        have hC : (0 : ℚ) ≤ (CΛ : ℚ) ^ 16 := by positivity
        calc (CΛ : ℚ) ^ 16 = (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (1 - ζ) ^ 16 := (div_mul_cancel₀ _ h1ζ.ne').symm
          _ ≤ (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (e ^ 16 * (Lq q : ℚ) ^ 3) := by
              apply mul_le_mul_of_nonneg_left ht.le (by positivity)
          _ = (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (Lq q : ℚ) ^ 3 * e ^ 16 := by ring
      have : (0 : ℚ) ≤ ((CΛ : ℚ) / (1 / 2 - ζ)) ^ 16 := by positivity
      linarith
  have hfinal : (rowBLambda h0 h1 CΛ q : ℚ) ^ 16 ≤ K0 * (Lq q : ℚ) ^ 3 := by
    have hc0 : (0 : ℚ) ≤ ((CΛ : ℚ) / (1 / 2 - ζ)) ^ 16 := by positivity
    have hc1 : (0 : ℚ) ≤ (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 := by positivity
    calc (rowBLambda h0 h1 CΛ q : ℚ) ^ 16 ≤ 2 ^ 16 * (a ^ 16 + 1) := hpow
      _ ≤ 2 ^ 16 * (((CΛ : ℚ) / (1 / 2 - ζ)) ^ 16 + (CΛ : ℚ) ^ 16 / (1 - ζ) ^ 16 * (Lq q : ℚ) ^ 3 + 1) := by
          gcongr
      _ ≤ K0 * (Lq q : ℚ) ^ 3 := by
          simp only [K0]
          nlinarith [mul_le_mul_of_nonneg_left hL3 hc0]
  have hK : K0 ≤ (⌈K0⌉₊ : ℚ) := Nat.le_ceil K0
  have : (rowBLambda h0 h1 CΛ q : ℚ) ^ 16 ≤ (⌈K0⌉₊ : ℚ) * (Lq q : ℚ) ^ 3 :=
    hfinal.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  exact_mod_cast this

theorem rowBSparse_pow8_le (CΛ Cδ : ℕ) : ∃ Csp : ℕ, ∀ q, rowBSparse h0 h1 CΛ Cδ q ^ 8 ≤ Csp * Lq q ^ 3 := by
  obtain ⟨K, hK⟩ := rowBLambda_pow16_le h0 h1 CΛ
  refine ⟨Cδ ^ 8 * K, fun q => ?_⟩
  calc rowBSparse h0 h1 CΛ Cδ q ^ 8 = Cδ ^ 8 * rowBLambda h0 h1 CΛ q ^ 16 := by
        unfold rowBSparse; ring
    _ ≤ Cδ ^ 8 * (K * Lq q ^ 3) := Nat.mul_le_mul_left _ (hK q)
    _ = Cδ ^ 8 * K * Lq q ^ 3 := by ring

end NearCubicWires.WireExponent3_5.Ledger

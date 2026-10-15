import Proof.Gates.Dispatch.ParamsD

set_option autoImplicit false

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter

theorem ceil_div_nat (a b : ℕ) (hb : 0 < b) : ⌈(a : ℚ) / b⌉₊ = (a + b - 1) / b := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  apply le_antisymm
  · apply Nat.ceil_le.2
    rw [div_le_iff₀ hbq]
    have h1 := Nat.div_add_mod (a + b - 1) b
    have h2 := Nat.mod_lt (a + b - 1) hb
    have : a ≤ (a + b - 1) / b * b := by
      have : b * ((a + b - 1) / b) = (a + b - 1) / b * b := mul_comm _ _
      omega
    exact_mod_cast this
  · have hc := Nat.le_ceil ((a : ℚ) / b)
    rw [div_le_iff₀ hbq] at hc
    have hc' : a ≤ ⌈(a : ℚ) / b⌉₊ * b := by exact_mod_cast hc
    have : (a + b - 1) / b < ⌈(a : ℚ) / b⌉₊ + 1 := by
      rw [Nat.div_lt_iff_lt_mul hb]
      rw [Nat.add_mul, one_mul]
      omega
    omega

theorem rat_div_reduce (A B : ℕ) (hB : 0 < B) :
    ((A : ℚ) / B).num = ((A / Nat.gcd A B : ℕ) : ℤ) ∧ ((A : ℚ) / B).den = B / Nat.gcd A B := by
  set g := Nat.gcd A B with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hB
  obtain ⟨a', ha⟩ := Nat.gcd_dvd_left A B
  obtain ⟨b', hb⟩ := Nat.gcd_dvd_right A B
  rw [← hg] at ha hb
  have hb' : 0 < b' := by rcases Nat.eq_zero_or_pos b' with h | h
                          · rw [h, mul_zero] at hb; omega
                          · exact h
  have hcop : Nat.Coprime a' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := A) (n := B) hg0
    rwa [← hg, ha, hb, Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hq : (A : ℚ) / B = ((a' : ℤ) : ℚ) / ((b' : ℤ) : ℚ) := by
    rw [ha, hb]; push_cast
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
    rw [mul_div_mul_left _ _ this]
  have hA : A / g = a' := by rw [ha, Nat.mul_div_cancel_left _ hg0]
  have hB' : B / g = b' := by rw [hb, Nat.mul_div_cancel_left _ hg0]
  rw [hA, hB', hq]
  have hb0 : (0 : ℤ) < (b' : ℤ) := by exact_mod_cast hb'
  have hc : Nat.Coprime (a' : ℤ).natAbs (b' : ℤ).natAbs := by simpa using hcop
  refine ⟨Rat.num_div_eq_of_coprime hb0 hc, ?_⟩
  have := Rat.den_div_eq_of_coprime hb0 hc
  exact_mod_cast this

/-- `ℓ₀ = Wk / (βR₀)` with `β = num/den`, `num > 0`, `R₀ > 0`. -/
theorem ell0_eq (W k R0 num den : ℕ) (β : ℚ) (hβ : β = (num : ℚ) / den) (hnum : 0 < num) (hden : 0 < den)
    (hR : 0 < R0) : ((W * k : ℕ) : ℚ) / (β * R0) = ((W * k * den : ℕ) : ℚ) / ((num * R0 : ℕ) : ℚ) := by
  rw [hβ]
  have h1 : (den : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have h2 : (num : ℚ) ≠ 0 := by exact_mod_cast hnum.ne'
  have h3 : (R0 : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  field_simp

/-- `ℓ̄ = max(ℓ₀, h²/(256T))` as an integer pair. -/
theorem ellBar_eq (A B h T : ℕ) (hB : 0 < B) (hT : 0 < T) :
    ellBar ((A : ℚ) / B) h T = (if h * h * B < A * 256 * T then ((A : ℚ) / B) else ((h * h : ℕ) : ℚ) / ((256 * T : ℕ) : ℚ)) := by
  unfold ellBar
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hTq : (0 : ℚ) < 256 * T := by positivity
  have key : (A : ℚ) / B ≤ (h : ℚ) ^ 2 / (256 * T) ↔ A * 256 * T ≤ h * h * B := by
    rw [div_le_div_iff₀ hBq hTq]
    constructor
    · intro h'; have : ((A * 256 * T : ℕ) : ℚ) ≤ ((h * h * B : ℕ) : ℚ) := by push_cast; nlinarith
      exact_mod_cast this
    · intro h'; have : ((A * 256 * T : ℕ) : ℚ) ≤ ((h * h * B : ℕ) : ℚ) := by exact_mod_cast h'
      push_cast at this; nlinarith
  rw [max_def]
  split_ifs with h1 h2 h2
  · exact absurd (key.1 h1) (by omega)
  · push_cast; ring
  · rfl
  · exact absurd (key.2 (by omega)) h1

/-- `M₁ = ⌈4ℓ̄/h⌉₊` and `x₁ = π₁/π*` for `ℓ̄ = EN/ED`. -/
theorem firstDen_eq (ell0 : ℚ) (h T EN ED : ℕ) (hb : ellBar ell0 h T = (EN : ℚ) / ED) (hED : 0 < ED) (hh : 0 < h) :
    firstDen ell0 h T = (4 * EN + ED * h - 1) / (ED * h) := by
  unfold firstDen
  rw [hb, ← ceil_div_nat (4 * EN) (ED * h) (by positivity)]
  congr 1
  push_cast
  have : (ED : ℚ) ≠ 0 := by exact_mod_cast hED.ne'
  have : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp

theorem firstRatio_eq (ell0 : ℚ) (h T EN ED : ℕ) (hb : ellBar ell0 h T = (EN : ℚ) / ED) (hED : 0 < ED)
    (hh : 0 < h) (hT : 0 < T) (hEN : 0 < EN) (hM : 0 < firstDen ell0 h T) :
    firstRatio ell0 h T = ((8 * T * EN : ℕ) : ℚ) / ((firstDen ell0 h T * (h * h) * ED : ℕ) : ℚ) := by
  unfold firstRatio piStar
  rw [hb]
  have : (ED : ℚ) ≠ 0 := by exact_mod_cast hED.ne'
  have : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  have : (EN : ℚ) ≠ 0 := by exact_mod_cast hEN.ne'
  have : (firstDen ell0 h T : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

/-- `factorRat` on a fraction below `1/256`. -/
theorem factorRat_eq_sqrt (N D : ℕ) (hN : 0 < N) (hlt : 256 * N < D) :
    RationalRateChain.factorRat ((N : ℚ) / D) = Nat.sqrt (D / (16 * N)) := by
  unfold RationalRateChain.factorRat
  have hD : 0 < D := by omega
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hP : ∀ a : ℕ, (16 * (a : ℚ) ^ 2 * ((N : ℚ) / D) ≤ 1 ↔ a ≤ Nat.sqrt (D / (16 * N))) := by
    intro a
    rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]
    rw [show 16 * (a : ℚ) ^ 2 * ((N : ℚ) / D) = ((16 * a ^ 2 * N : ℕ) : ℚ) / D by push_cast; ring]
    rw [div_le_one hDq]
    rw [show a * a * (16 * N) = 16 * a ^ 2 * N by ring]
    exact_mod_cast Iff.rfl
  have hle : Nat.sqrt (D / (16 * N)) ≤ ⌈1 / ((N : ℚ) / D)⌉₊ := by
    have h1 : Nat.sqrt (D / (16 * N)) ≤ D / (16 * N) := Nat.sqrt_le_self _
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have h3 : ((D / (16 * N) : ℕ) : ℚ) ≤ 1 / ((N : ℚ) / D) := by
      rw [one_div_div]
      refine le_trans (Nat.cast_div_le) ?_
      push_cast
      exact div_le_div_of_nonneg_left (by positivity) hNq (by linarith)
    have h4 : ((D / (16 * N) : ℕ) : ℚ) ≤ (⌈1 / ((N : ℚ) / D)⌉₊ : ℚ) := le_trans h3 (Nat.le_ceil _)
    have : D / (16 * N) ≤ ⌈1 / ((N : ℚ) / D)⌉₊ := by exact_mod_cast h4
    omega
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hle, fun _ => (hP _).2 le_rfl, fun k hk _ hk2 => ?_⟩
  exact absurd ((hP k).1 hk2) (by omega)

/-- One chain step on a fraction `N/D` below `1/256`. -/
theorem ratio_succ_lt (x : ℚ) (i N D : ℕ) (hr : RationalRateChain.ratio x i = (N : ℚ) / D) (hN : 0 < N)
    (hlt : 256 * N < D) :
    RationalRateChain.ratio x (i + 1) = ((Nat.sqrt (D / (16 * N)) * N : ℕ) : ℚ) / D ∧
    RationalRateChain.factorRat (RationalRateChain.ratio x i) = Nat.sqrt (D / (16 * N)) := by
  have hD : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  have hsmall : RationalRateChain.ratio x i < 1 / 256 := by
    rw [hr, div_lt_div_iff₀ hD (by norm_num)]
    have : ((256 * N : ℕ) : ℚ) < (D : ℚ) := by exact_mod_cast hlt
    push_cast at this; linarith
  refine ⟨?_, by rw [hr, factorRat_eq_sqrt N D hN hlt]⟩
  rw [RationalRateChain.ratio, if_pos hsmall, hr, factorRat_eq_sqrt N D hN hlt]
  push_cast; ring

theorem ratio_ge_iff (N D : ℕ) (hD : 0 < D) : (1 : ℚ) / 256 ≤ (N : ℚ) / D ↔ D ≤ 256 * N := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  rw [div_le_div_iff₀ (by norm_num) hDq]
  constructor
  · intro h; have : ((D : ℕ) : ℚ) ≤ ((256 * N : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  · intro h; have : ((D : ℕ) : ℚ) ≤ ((256 * N : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this; linarith

end NearCubicGates.Close.Dispatch

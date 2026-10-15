import Proof.Wire_3_5.LedgerGrowth

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

def capExp32 : Mode → ℕ
  | .thr => 174
  | .sym => 142

structure CapParams where
  aT : ℕ
  aS : ℕ
  betaInv : ℕ
  Cpar : ℕ

/-- The native coefficient of a class mode. -/
def CapParams.coef (C : CapParams) : Mode → ℕ
  | .thr => C.aT
  | .sym => C.aS

noncomputable def wireCap (C : CapParams) (m : Mode) (q : ℕ) : ℝ :=
  C.coef m * (q : ℝ) ^ 3 * Real.sqrt q / (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32)

/-- The 32nd power of `β⁻¹ C_0 r^{3/2} s a_i q²`, times nothing: its quotient by `L^{32 K_i}` is the main term's 32nd
power. -/
def capMainNum (C : CapParams) (m : Mode) (r s q : ℕ) : ℕ :=
  2 ^ 80 * r ^ 48 * s ^ 32 * C.coef m ^ 32 * q ^ 64 * C.betaInv ^ 32

/-- The main term's 32nd power `⌈(β⁻¹ C_0 r^{3/2} s a_i q²)^{32}/L^{32 K_i}⌉`. -/
def capMainPow (C : CapParams) (m : Mode) (r s q : ℕ) : ℕ :=
  (capMainNum C m r s q + Lq q ^ capExp32 m - 1) / Lq q ^ capExp32 m

/-- The encoding term's square `(β⁻¹ C_0 r^{3/2} C_par q^{1/2})² = 32 r³ C_par² q β⁻²`. -/
def capEncPow (C : CapParams) (r q : ℕ) : ℕ := 32 * r ^ 3 * C.Cpar ^ 2 * q * C.betaInv ^ 2

def rowBCap (C : CapParams) (m : Mode) (r s q : ℕ) : ℕ :=
  1 + ceilRoot 31 (capMainPow C m r s q) + ceilRoot 1 (capEncPow C r q)

theorem one_le_rowBCap (C : CapParams) (m : Mode) (r s q : ℕ) : 1 ≤ rowBCap C m r s q := by
  unfold rowBCap; omega

theorem Lq_pow_pos (m : Mode) (q : ℕ) : 0 < Lq q ^ capExp32 m := pow_pos (Lq_pos q) _

/-- The ceiling quotient: `N ≤ ⌈N/D⌉·D`. -/
theorem le_ceilDiv_mul (N D : ℕ) (hD : 0 < D) : N ≤ (N + D - 1) / D * D := by
  have h := Nat.lt_div_mul_add (a := N + D - 1) hD
  omega

theorem capMain_complete (C : CapParams) (m : Mode) (r s q : ℕ) :
    capMainNum C m r s q ≤ ceilRoot 31 (capMainPow C m r s q) ^ 32 * Lq q ^ capExp32 m := by
  have h1 : capMainNum C m r s q ≤ capMainPow C m r s q * Lq q ^ capExp32 m :=
    le_ceilDiv_mul _ _ (Lq_pow_pos m q)
  exact h1.trans (Nat.mul_le_mul_right _ (le_ceilRoot_pow 31 _))

/-- The encoding term, in integers. -/
theorem capEnc_complete (C : CapParams) (r q : ℕ) : capEncPow C r q ≤ ceilRoot 1 (capEncPow C r q) ^ 2 :=
  le_ceilRoot_pow 1 _

/-- The main term's quotient is at most `N/L^{32K} + 1`: `capMainPow·L^{32K} ≤ N + L^{32K}`. -/
theorem capMainPow_mul_le (C : CapParams) (m : Mode) (r s q : ℕ) :
    capMainPow C m r s q * Lq q ^ capExp32 m ≤ capMainNum C m r s q + Lq q ^ capExp32 m := by
  unfold capMainPow
  have := Nat.div_mul_le_self (capMainNum C m r s q + Lq q ^ capExp32 m - 1) (Lq q ^ capExp32 m)
  omega

theorem four_sqrt_two_pow_32 : (4 * Real.sqrt 2) ^ 32 = (2 : ℝ) ^ 80 := by
  have h : (4 * Real.sqrt 2) ^ 2 = (32 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  calc (4 * Real.sqrt 2) ^ 32 = ((4 * Real.sqrt 2) ^ 2) ^ 16 := by rw [← pow_mul]
    _ = (2 : ℝ) ^ 80 := by rw [h]; norm_num

theorem sqrt_pow_32 (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 32 = x ^ 16 := by
  rw [show (32 : ℕ) = 2 * 16 from rfl, pow_mul, Real.sq_sqrt hx]

theorem mul_sqrt_pow_32 (x : ℝ) (hx : 0 ≤ x) : (x * Real.sqrt x) ^ 32 = x ^ 48 := by
  rw [mul_pow, sqrt_pow_32 x hx]; ring

/-- The rearrangement of `tr:population`'s right side, in `t = √q`. -/
theorem cap_rearrange (A s a c Lk t : ℝ) (ht : 0 < t) (hL : 0 < Lk) :
    A * (s * (a * (t ^ 2) ^ 3 * t / Lk) + c * (t ^ 2) ^ 2) / (t ^ 2 * t) =
      A * s * a * (t ^ 2) ^ 2 / Lk + A * c * t := by
  field_simp

theorem rpow_div32_pow_32 (L : ℝ) (hL : 0 ≤ L) (K : ℕ) : (L ^ ((K : ℝ) / 32)) ^ 32 = L ^ K := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

theorem rowBCap_complete (C : CapParams) (m : Mode) (r s q : ℕ) (hq : 1 ≤ q) (hβ : 1 ≤ C.betaInv) :
    4 * Real.sqrt 2 * ((r : ℝ) * Real.sqrt r) * ((s : ℝ) * wireCap C m q + C.Cpar * (q : ℝ) ^ 2) /
        ((q : ℝ) * Real.sqrt q) ≤ (rowBCap C m r s q : ℝ) / C.betaInv := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq'
  have hb : (0 : ℝ) < C.betaInv := by exact_mod_cast hβ
  have hL : (0 : ℝ) < (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) := by
    have : (0 : ℝ) < Lq q := by exact_mod_cast Lq_pos q
    positivity
  set Lk := (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) with hLk
  set X : ℝ := C.betaInv * (4 * Real.sqrt 2) * ((r : ℝ) * Real.sqrt r) * s * C.coef m * (q : ℝ) ^ 2 / Lk
  set Y : ℝ := C.betaInv * (4 * Real.sqrt 2) * ((r : ℝ) * Real.sqrt r) * C.Cpar * Real.sqrt q
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r

  have hX0 : 0 ≤ X := by positivity
  have hX : X ≤ ceilRoot 31 (capMainPow C m r s q) := by
    have hpow : X ^ 32 ≤ ((ceilRoot 31 (capMainPow C m r s q) : ℕ) : ℝ) ^ 32 := by
      have hint := capMain_complete C m r s q
      have hD : (0 : ℝ) < ((Lq q ^ capExp32 m : ℕ) : ℝ) := by exact_mod_cast Lq_pow_pos m q
      have hXp : X ^ 32 * ((Lq q ^ capExp32 m : ℕ) : ℝ) = (capMainNum C m r s q : ℝ) := by
        have hLk32 : Lk ^ 32 = ((Lq q ^ capExp32 m : ℕ) : ℝ) := by
          rw [hLk, rpow_div32_pow_32 _ (Nat.cast_nonneg _)]; push_cast; rfl
        have hX32 : X ^ 32 = (C.betaInv : ℝ) ^ 32 * (4 * Real.sqrt 2) ^ 32 * ((r : ℝ) * Real.sqrt r) ^ 32 *
            (s : ℝ) ^ 32 * (C.coef m : ℝ) ^ 32 * (q : ℝ) ^ 64 / Lk ^ 32 := by
          simp only [X]; ring
        rw [hX32, four_sqrt_two_pow_32, mul_sqrt_pow_32 _ hr0, hLk32, div_mul_cancel₀ _ hD.ne']
        simp only [capMainNum]; push_cast; ring
      have hRp : ((ceilRoot 31 (capMainPow C m r s q) : ℕ) : ℝ) ^ 32 * ((Lq q ^ capExp32 m : ℕ) : ℝ) ≥
          (capMainNum C m r s q : ℝ) := by exact_mod_cast hint
      nlinarith
    exact (pow_le_pow_iff_left₀ hX0 (Nat.cast_nonneg _) (by norm_num)).mp hpow

  have hY0 : 0 ≤ Y := by positivity
  have hY : Y ≤ ceilRoot 1 (capEncPow C r q) := by
    have hpow : Y ^ 2 ≤ ((ceilRoot 1 (capEncPow C r q) : ℕ) : ℝ) ^ 2 := by
      have hint := capEnc_complete C r q
      have hYp : Y ^ 2 = (capEncPow C r q : ℝ) := by
        have hY2 : Y ^ 2 = (C.betaInv : ℝ) ^ 2 * 16 * Real.sqrt 2 ^ 2 * (r : ℝ) ^ 2 * Real.sqrt r ^ 2 *
            (C.Cpar : ℝ) ^ 2 * Real.sqrt q ^ 2 := by
          simp only [Y]; ring
        rw [hY2, Real.sq_sqrt (by norm_num), Real.sq_sqrt hr0, Real.sq_sqrt (Nat.cast_nonneg q)]
        simp only [capEncPow]; push_cast; ring
      rw [hYp]; exact_mod_cast hint
    exact (pow_le_pow_iff_left₀ hY0 (Nat.cast_nonneg _) (by norm_num)).mp hpow
  -- assemble
  have hsum : (4 * Real.sqrt 2 * ((r : ℝ) * Real.sqrt r) * ((s : ℝ) * wireCap C m q + C.Cpar * (q : ℝ) ^ 2) /
      ((q : ℝ) * Real.sqrt q)) * C.betaInv = X + Y := by
    have key := cap_rearrange (4 * Real.sqrt 2 * ((r : ℝ) * Real.sqrt r)) s (C.coef m) C.Cpar Lk (Real.sqrt q)
      hsq hL
    rw [Real.sq_sqrt hq'.le] at key
    simp only [wireCap]
    rw [← hLk]
    have e : (s : ℝ) * (C.coef m * (q : ℝ) ^ 3 * Real.sqrt q / Lk) = (s : ℝ) * ((C.coef m : ℝ) * (q : ℝ) ^ 3 *
        Real.sqrt q / Lk) := rfl
    rw [key]
    simp only [X, Y]; ring
  rw [le_div_iff₀ hb, hsum]
  have : (rowBCap C m r s q : ℝ) = 1 + (ceilRoot 31 (capMainPow C m r s q) : ℝ) +
      (ceilRoot 1 (capEncPow C r q) : ℝ) := by unfold rowBCap; push_cast; ring
  rw [this]; linarith

end NearCubicWires.WireExponent3_5.Ledger

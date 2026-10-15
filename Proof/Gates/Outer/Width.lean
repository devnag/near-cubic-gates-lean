import Proof.Gates.Outer.Interface

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires

/-- `⌈log₂ T_clk(N)⌉`, `T_clk(N) = N^{k+2}`. -/
def clkLog (k N : ℕ) : ℕ := Nat.clog 2 (N ^ (k + 2))

/-- `q(N) = ⌈log₂ T_clk(N)⌉ + A ⌈log₂(⌈log₂ T_clk(N)⌉ + 2)⌉ + A`. -/
def widthOf (k A N : ℕ) : ℕ := clkLog k N + A * Nat.clog 2 (clkLog k N + 2) + A

/-- `A_pad` for the envelope constants `K`, `c`, `e` (chosen after them: paper App. C, the constant order, item 6, "An integer A_pad ≥ c_ℓ …"). -/
def padConst (K c e : ℕ) : ℕ := e + K * c * Nat.clog 2 (c + 2) ^ e

theorem clog_two_mul_pow_le (a l : ℕ) : Nat.clog 2 (a * 2 ^ l) ≤ Nat.clog 2 a + l := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) a)

/-- The arithmetic behind `ℓ_out ≤ q(N)`. -/
theorem envelope_le (K c e k N : ℕ) (hN : 1 ≤ N) :
    K * (c * N ^ (k + 2)) * logScale (c * N ^ (k + 2)) ^ e ≤ 2 ^ widthOf k (padConst K c e) N := by
  set lam := clkLog k N with hlam
  set mu := Nat.clog 2 (lam + 2) with hmu
  set κ := Nat.clog 2 (c + 2) with hκ
  set A := padConst K c e with hA
  have hNpow : 1 ≤ N ^ (k + 2) := Nat.one_le_pow _ _ hN
  have hT : N ^ (k + 2) ≤ 2 ^ lam := Nat.le_pow_clog (by norm_num) _
  have hκ1 : 1 ≤ κ := by
    rw [hκ]
    exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
  have hmu2 : lam + 2 ≤ 2 ^ mu := Nat.le_pow_clog (by norm_num) _
  -- the logarithmic factor
  have hL : logScale (c * N ^ (k + 2)) ≤ κ * (lam + 2) := by
    unfold logScale
    have h1 : c * N ^ (k + 2) + 2 ≤ (c + 2) * 2 ^ lam := by
      calc c * N ^ (k + 2) + 2 ≤ (c + 2) * N ^ (k + 2) := by nlinarith
        _ ≤ (c + 2) * 2 ^ lam := Nat.mul_le_mul_left _ hT
    calc Nat.clog 2 (c * N ^ (k + 2) + 2) ≤ Nat.clog 2 ((c + 2) * 2 ^ lam) := Nat.clog_mono_right _ h1
      _ ≤ κ + lam := clog_two_mul_pow_le _ _
      _ ≤ κ * (lam + 2) := by nlinarith
  have hLe : logScale (c * N ^ (k + 2)) ^ e ≤ κ ^ e * 2 ^ (mu * e) := by
    calc logScale (c * N ^ (k + 2)) ^ e ≤ (κ * (lam + 2)) ^ e := Nat.pow_le_pow_left hL _
      _ = κ ^ e * (lam + 2) ^ e := by rw [mul_pow]
      _ ≤ κ ^ e * (2 ^ mu) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmu2 _)
      _ = κ ^ e * 2 ^ (mu * e) := by rw [← pow_mul]
  have hAe : e ≤ A := by rw [hA, padConst]; omega
  have hAK : K * c * κ ^ e ≤ 2 ^ A := by
    have : K * c * κ ^ e ≤ A := by rw [hA, padConst, ← hκ]; omega
    exact this.trans (Nat.lt_two_pow_self).le
  have hmuA : 2 ^ (mu * e) ≤ 2 ^ (A * mu) :=
    Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_comm A]; exact Nat.mul_le_mul_left _ hAe)
  calc K * (c * N ^ (k + 2)) * logScale (c * N ^ (k + 2)) ^ e
      ≤ K * (c * 2 ^ lam) * (κ ^ e * 2 ^ (mu * e)) := by
        gcongr
    _ = (K * c * κ ^ e) * 2 ^ lam * 2 ^ (mu * e) := by ring
    _ ≤ 2 ^ A * 2 ^ lam * 2 ^ (A * mu) := by gcongr
    _ = 2 ^ widthOf k A N := by
        rw [widthOf, ← hlam, ← hmu, pow_add, pow_add]
        ring

/-- `ν + 1 ≤ q(2^ν)`: the source index fits in the width (CHECK reads `ν` of the `q` bits). -/
theorem succ_le_widthOf (k A ν : ℕ) (hA : 1 ≤ A) : ν + 1 ≤ widthOf k A (2 ^ ν) := by
  have hlam : ν ≤ clkLog k (2 ^ ν) := by
    unfold clkLog
    rw [← pow_mul, Nat.clog_pow 2 _ (by norm_num)]
    nlinarith
  unfold widthOf
  nlinarith

theorem clkLog_two_pow (k ν : ℕ) : clkLog k (2 ^ ν) = ν * (k + 2) := by
  unfold clkLog
  rw [← pow_mul, Nat.clog_pow 2 _ (by norm_num)]

theorem clog_add_le (x d : ℕ) (hx : 1 ≤ x) : Nat.clog 2 (x + d) ≤ Nat.clog 2 x + d := by
  apply Nat.clog_le_of_le_pow
  have h1 : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  have h2 : 1 + d ≤ 2 ^ d := by
    have := Nat.lt_two_pow_self (n := d)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · have : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
      omega
  rw [pow_add]
  calc x + d ≤ x * (1 + d) := by nlinarith
    _ ≤ 2 ^ Nat.clog 2 x * 2 ^ d := Nat.mul_le_mul h1 h2

/-- One doubling of `N` moves `q(N)` by at most `(k+2)(A+1)` (bounded additive jumps, paper v2 §11.6). -/
theorem widthOf_step (k A ν : ℕ) : widthOf k A (2 ^ (ν + 1)) ≤ widthOf k A (2 ^ ν) + (k + 2) * (A + 1) := by
  unfold widthOf
  rw [clkLog_two_pow, clkLog_two_pow]
  have h := clog_add_le (ν * (k + 2) + 2) (k + 2) (by omega)
  have heq : (ν + 1) * (k + 2) + 2 = ν * (k + 2) + 2 + (k + 2) := by ring
  rw [heq]
  nlinarith

/-- Once `2^T ≤ N`, `q(N) ≥ T` (the native width dominates every fixed threshold eventually). -/
theorem le_widthOf (k A T N : ℕ) (hN : 2 ^ T ≤ N) : T ≤ widthOf k A N := by
  have h1 : T ≤ clkLog k N := by
    unfold clkLog
    refine le_trans ?_ (Nat.log_le_clog 2 _)
    apply Nat.le_log_of_pow_le (by norm_num)
    calc 2 ^ T ≤ N := hN
      _ ≤ N ^ (k + 2) := Nat.le_self_pow (by omega) N
  unfold widthOf
  omega

theorem two_pow_clog_le (x : ℕ) : 2 ^ Nat.clog 2 x ≤ 2 * x + 1 := by
  rcases Nat.lt_or_ge x 2 with hx | hx
  · interval_cases x <;> simp [Nat.clog]
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < x)
    rw [Nat.pred_eq_sub_one] at h
    have hc : 1 ≤ Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
    have : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- **`2^{q(N)}` is polynomial in `N`** (paper v2 §11.4: `2^q/T_clk(N) = q^{O(1)}`). -/
theorem widthOf_pow (k A : ℕ) : ∃ C m : ℕ, ∀ N, 2 ^ widthOf k A N ≤ C * (N + 1) ^ m := by
  refine ⟨2 ^ A * 3 * 11 ^ A, (k + 2) * (A + 1), fun N => ?_⟩
  set T := (N + 1) ^ (k + 2) with hT
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  have hc : clkLog k N ≤ Nat.clog 2 T := Nat.clog_mono_right _ (Nat.pow_le_pow_left (by omega) _)
  have h1 : 2 ^ clkLog k N ≤ 3 * T := by
    have := two_pow_clog_le T
    exact (Nat.pow_le_pow_right (by norm_num) hc).trans (by omega)
  have h2 : 2 ^ Nat.clog 2 (clkLog k N + 2) ≤ 11 * T := by
    have hcl : clkLog k N + 2 ≤ 3 * T + 2 := by
      have h0 : clkLog k N < 2 ^ clkLog k N := Nat.lt_two_pow_self
      exact Nat.add_le_add_right (h0.le.trans h1) 2
    calc 2 ^ Nat.clog 2 (clkLog k N + 2) ≤ 2 ^ Nat.clog 2 (3 * T + 2) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right _ hcl)
      _ ≤ 2 * (3 * T + 2) + 1 := two_pow_clog_le _
      _ ≤ 11 * T := by omega
  unfold widthOf
  rw [pow_add, pow_add, pow_mul', Nat.mul_comm]
  calc 2 ^ A * (2 ^ clkLog k N * (2 ^ Nat.clog 2 (clkLog k N + 2)) ^ A)
      ≤ 2 ^ A * (3 * T * (11 * T) ^ A) := by gcongr
    _ = 2 ^ A * 3 * 11 ^ A * T ^ (A + 1) := by rw [mul_pow, pow_succ]; ring
    _ = 2 ^ A * 3 * 11 ^ A * (N + 1) ^ ((k + 2) * (A + 1)) := by rw [hT, ← pow_mul]

/-- **`2^{q(N)} ≤ C·N^{k+2}·q^A`** (paper v2 §11.4: "`2^q/T_clk(N) = q^{O(1)}`"), the table bound of the weak machine's
runtime split. -/
theorem widthOf_table (k A N : ℕ) (hN : 1 ≤ N) (hA : 1 ≤ A) :
    2 ^ widthOf k A N ≤ 3 * 12 ^ A * N ^ (k + 2) * widthOf k A N ^ A := by
  set T := N ^ (k + 2) with hT
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  set c := clkLog k N with hc
  set q := widthOf k A N with hq
  have h1 : 2 ^ c ≤ 3 * T := (two_pow_clog_le T).trans (by omega)
  have hcl1 : 1 ≤ Nat.clog 2 (c + 2) := Nat.clog_pos (by norm_num) (by omega)
  have hcq : c + 2 ≤ 2 * q := by
    have : c + A * Nat.clog 2 (c + 2) + A = q := by rw [hq, widthOf]
    have : A * 1 ≤ A * Nat.clog 2 (c + 2) := Nat.mul_le_mul_left _ hcl1
    omega
  have h2 : 2 ^ Nat.clog 2 (c + 2) ≤ 6 * q := (two_pow_clog_le (c + 2)).trans (by omega)
  have hqdef : q = c + A * Nat.clog 2 (c + 2) + A := by rw [hq, widthOf]
  rw [hqdef, pow_add, pow_add, pow_mul']
  rw [← hqdef]
  calc 2 ^ c * (2 ^ Nat.clog 2 (c + 2)) ^ A * 2 ^ A ≤ (3 * T) * (6 * q) ^ A * 2 ^ A := by gcongr
    _ = 3 * 12 ^ A * T * q ^ A := by
        rw [mul_pow, show (12 : ℕ) = 6 * 2 by norm_num, mul_pow]; ring

end NearCubicGates.Close.Outer

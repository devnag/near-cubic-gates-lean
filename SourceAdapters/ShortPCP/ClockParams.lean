import NineInputs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Clock parameters and conditional polynomial estimates

`lem:tm-ram` chooses `w_n` as the least power of two above `⌈lg T(n)⌉ + c_V`,
pads the input to the least power of two above `max(n+1,w_n)`, and chooses `T_n`
as the least power of two above `c_V(T(n)+w_n)`. Its proof's "Constants" paragraph
bounds the padded input and places the run and every address below `2^{w_n}`.
Here the supplied clock `t` replaces `T(n)`, as in `cor:short-pcp-clock`.

The last section proves conditional arithmetic estimates for field cardinalities
and neighbor counts from explicitly supplied bounds. The current affine reduction
obtains its field and degree bounds from `lem:acsp-degree`; these conditional
lemmas do not assert those hypotheses for a reduction.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicWires

/-- `w_n`: the least power of two `≥ ⌈lg t⌉ + c`. -/
def wordWidth (c t : ℕ) : ℕ := 2 ^ Nat.clog 2 (Nat.clog 2 t + c)

/-- `log T_n`: the exponent of the least power of two above `c·(t + w_n)` (`lem:tm-ram`). -/
def timeExp (c t : ℕ) : ℕ := Nat.clog 2 (c * (t + wordWidth c t))

/-- `T_n = 2^{timeExp}`. -/
def padTime (c t : ℕ) : ℕ := 2 ^ timeExp c t

/-- `|x̄| = 2^{⌈lg max(n+1, w_n)⌉}`. -/
def inputPadLength (c n t : ℕ) : ℕ := 2 ^ Nat.clog 2 (max (n + 1) (wordWidth c t))

/-! ## The least power of two -/

theorem le_two_pow_clog (x : ℕ) : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x

/-- The least power of two `≥ x` is below `2x` (for `x ≥ 1`). -/
theorem two_pow_clog_lt (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x < 2 * x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hpos := Nat.clog_pos (b := 2) (by norm_num) h
    have : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x).pred := by
      rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hpos).symm
    omega
  · have : x = 1 := by omega
    subst this
    simp

theorem pow_le_pow_iff {a b : ℕ} : 2 ^ a ≤ 2 ^ b ↔ a ≤ b := pow_le_pow_iff_right₀ (by norm_num)

/-- `logScale t = ⌈lg (t+2)⌉` is at least `1`, at least `⌈lg t⌉`, at most `t + 2`, and `t < 2^{logScale t}`. -/
theorem logScale_facts (t : ℕ) :
    1 ≤ logScale t ∧ Nat.clog 2 t ≤ logScale t ∧ logScale t ≤ t + 2 ∧ t < 2 ^ logScale t := by
  unfold logScale
  refine ⟨Nat.clog_pos (by norm_num) (by omega), Nat.clog_mono_right 2 (by omega), ?_, ?_⟩
  · have hpos := Nat.clog_pos (b := 2) (by norm_num) (show 1 < t + 2 by omega)
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < t + 2 by omega)
    have := Nat.lt_two_pow_self (n := (Nat.clog 2 (t + 2)).pred)
    have hs : Nat.clog 2 (t + 2) = (Nat.clog 2 (t + 2)).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
    omega
  · have := le_two_pow_clog (t + 2)
    omega

/-! ## `lem:tm-ram`'s constants -/

theorem wordWidth_ge (c t : ℕ) : Nat.clog 2 t + c ≤ wordWidth c t := le_two_pow_clog _

theorem wordWidth_lt (c t : ℕ) (hc : 1 ≤ c) : wordWidth c t < 2 * (Nat.clog 2 t + c) :=
  two_pow_clog_lt _ (by omega)

theorem padTime_ge (c t : ℕ) : c * (t + wordWidth c t) ≤ padTime c t := le_two_pow_clog _

theorem padTime_lt (c t : ℕ) (hc : 1 ≤ c) : padTime c t < 2 * (c * (t + wordWidth c t)) := by
  have := wordWidth_ge c t
  exact two_pow_clog_lt _ (Nat.mul_pos (by omega) (by omega))

/-- `w_n ≤ (6 + 2c)·t` for `t ≥ 1`. -/
theorem wordWidth_le_linear (c t : ℕ) (hc : 1 ≤ c) (ht : 1 ≤ t) : wordWidth c t ≤ (6 + 2 * c) * t := by
  have h1 := wordWidth_lt c t hc
  have h2 := (logScale_facts t).2.1
  have h3 := (logScale_facts t).2.2.1
  nlinarith

/-- "`T_n = O(t + log t)`" (`lem:tm-ram` and its proof): `T_n ≤ 2c(7 + 2c)·t` for `t ≥ 1`. -/
theorem padTime_le_linear (c t : ℕ) (hc : 1 ≤ c) (ht : 1 ≤ t) : padTime c t ≤ 2 * c * (7 + 2 * c) * t := by
  have h1 := padTime_lt c t hc
  have h2 := wordWidth_le_linear c t hc ht
  nlinarith

theorem key_const (c : ℕ) (hc : 16 ≤ c) : 2 * c * (7 + 2 * c) < 2 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
    rw [pow_succ]
    nlinarith

/-- "`2^{w_n} ≥ 2^{c_V} T(n)` is larger than `T_n`" (`lem:tm-ram` and its proof). -/
theorem two_pow_wordWidth (c t : ℕ) (hc : 16 ≤ c) (ht : 1 ≤ t) :
    2 ^ c * t ≤ 2 ^ wordWidth c t ∧ padTime c t < 2 ^ wordWidth c t := by
  have hw := wordWidth_ge c t
  have h1 : 2 ^ c * t ≤ 2 ^ wordWidth c t := by
    calc 2 ^ c * t ≤ 2 ^ c * 2 ^ Nat.clog 2 t := Nat.mul_le_mul_left _ (le_two_pow_clog t)
      _ = 2 ^ (Nat.clog 2 t + c) := by rw [pow_add, mul_comm]
      _ ≤ 2 ^ wordWidth c t := pow_le_pow_iff.mpr hw
  refine ⟨h1, ?_⟩
  have h2 := padTime_le_linear c t (by omega) ht
  have h3 := key_const c hc
  calc padTime c t ≤ 2 * c * (7 + 2 * c) * t := h2
    _ < 2 ^ c * t := Nat.mul_lt_mul_of_pos_right h3 ht
    _ ≤ _ := h1

/-- `T_n` is a power of two, at least `16`, and a multiple of `8` (the idle loop's requirements, `lem:tm-ram` and its proof). -/
theorem padTime_shape (c t : ℕ) (hc : 16 ≤ c) (ht : 1 ≤ t) :
    16 ≤ padTime c t ∧ 8 ∣ padTime c t ∧ 4 ≤ timeExp c t := by
  have h16 : 16 ≤ padTime c t := by
    have := padTime_ge c t
    nlinarith [wordWidth_ge c t]
  have h4 : 4 ≤ timeExp c t := by
    by_contra h
    have : padTime c t ≤ 2 ^ 3 := by
      unfold padTime; exact pow_le_pow_iff.mpr (by omega)
    omega
  refine ⟨h16, ?_, h4⟩
  unfold padTime
  exact ⟨2 ^ (timeExp c t - 3), by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (timeExp c t - 3) = timeExp c t by omega]⟩

/-- `|x̄|`: a power of two, a multiple of `w_n`, at least `n + 1`, and "`|x̄| ≤ 2(n+1) + 2w_n ≤ T_n`"
(`lem:tm-ram` and its proof), for `1 ≤ n ≤ t`. -/
theorem inputPad_facts (c n t : ℕ) (hc : 16 ≤ c) (hn : 1 ≤ n) (hnt : n ≤ t) :
    n + 1 ≤ inputPadLength c n t ∧ wordWidth c t ∣ inputPadLength c n t ∧
      inputPadLength c n t ≤ 2 * (n + 1) + 2 * wordWidth c t ∧
      2 * (n + 1) + 2 * wordWidth c t ≤ padTime c t := by
  have hmax := le_two_pow_clog (max (n + 1) (wordWidth c t))
  have hlt := two_pow_clog_lt (max (n + 1) (wordWidth c t)) (by omega)
  refine ⟨by unfold inputPadLength; omega, ?_, by unfold inputPadLength; omega, ?_⟩
  · have hm : Nat.clog 2 (wordWidth c t) = Nat.clog 2 (Nat.clog 2 t + c) := Nat.clog_pow 2 _ (by norm_num)
    have hle : Nat.clog 2 (Nat.clog 2 t + c) ≤ Nat.clog 2 (max (n + 1) (wordWidth c t)) :=
      hm ▸ Nat.clog_mono_right 2 (le_max_right _ _)
    exact Nat.pow_dvd_pow 2 hle
  · have := padTime_ge c t
    nlinarith

/-! ## Conditional field-size and neighbor-count estimates -/

/-- `log T_n ≤ logScale t + 2c(7+2c)` for `t ≥ 1`. -/
theorem timeExp_le (c t : ℕ) (hc : 1 ≤ c) (ht : 1 ≤ t) :
    timeExp c t ≤ logScale t + 2 * c * (7 + 2 * c) := by
  have h1 := padTime_le_linear c t hc ht
  have h2 := (logScale_facts t).2.2.2
  have h3 := Nat.lt_two_pow_self (n := 2 * c * (7 + 2 * c))
  have : padTime c t ≤ 2 ^ (logScale t + 2 * c * (7 + 2 * c)) := by
    rw [pow_add]
    calc padTime c t ≤ 2 * c * (7 + 2 * c) * t := h1
      _ ≤ 2 ^ (2 * c * (7 + 2 * c)) * 2 ^ logScale t := by
        rw [mul_comm (2 ^ _)]; exact Nat.mul_le_mul h3.le h2.le |>.trans (by rw [mul_comm])
      _ = 2 ^ logScale t * 2 ^ (2 * c * (7 + 2 * c)) := by ring
  exact pow_le_pow_iff.mp this

/-- **Conditional field size.** If `d ≤ A(w_n+1)^B` and the field cardinality obeys
`2^f ≤ C·(log T_n + k w_n + 1)·(log T_n + 1)·(d+1)·T_n`, then
`2^f ≤ K·t·logScale(t)^e`, with `K,e` depending only on `C,k,c,A,B`. -/
theorem field_instantiation (C k c A B : ℕ) (hc : 1 ≤ c) :
    ∃ K e : ℕ, ∀ t f d : ℕ, 1 ≤ t → d ≤ A * (wordWidth c t + 1) ^ B →
      2 ^ f ≤ C * (timeExp c t + k * wordWidth c t + 1) * (timeExp c t + 1) * (d + 1) * 2 ^ timeExp c t →
      2 ^ f ≤ K * t * logScale t ^ e := by
  set a := 2 * c * (7 + 2 * c)
  set P := a + 2 * k * c + 2 * k + 2 * c + 3
  refine ⟨C * (P * P) * ((A + 1) * P ^ B) * a, 2 + B, fun t f d ht hd hF => ?_⟩
  obtain ⟨hL1, hLc, -, -⟩ := logScale_facts t
  set L := logScale t
  have hτ : timeExp c t ≤ L + a := timeExp_le c t hc ht
  have hw : wordWidth c t < 2 * (L + c) := by have := wordWidth_lt c t hc; omega
  have hT : 2 ^ timeExp c t ≤ a * t := padTime_le_linear c t hc ht
  have haL : a ≤ a * L := Nat.le_mul_of_pos_right a hL1
  have hkcL : 2 * k * c ≤ 2 * k * c * L := Nat.le_mul_of_pos_right _ hL1
  have hcL : 2 * c ≤ 2 * c * L := Nat.le_mul_of_pos_right _ hL1
  have hPL : P * L = a * L + 2 * k * c * L + 2 * k * L + 2 * c * L + 3 * L := by
    simp only [P]; ring
  have f1 : timeExp c t + k * wordWidth c t + 1 ≤ P * L := by
    have : k * wordWidth c t ≤ k * (2 * (L + c)) := Nat.mul_le_mul_left _ hw.le
    have e : k * (2 * (L + c)) = 2 * k * L + 2 * k * c := by ring
    omega
  have f2 : timeExp c t + 1 ≤ P * L := by omega
  have f3 : d + 1 ≤ (A + 1) * (P * L) ^ B := by
    have hwP : wordWidth c t + 1 ≤ P * L := by omega
    have hpow : (wordWidth c t + 1) ^ B ≤ (P * L) ^ B := Nat.pow_le_pow_left hwP B
    have hone : 1 ≤ (P * L) ^ B := Nat.one_le_pow _ _ (by positivity)
    nlinarith
  calc 2 ^ f ≤ C * (timeExp c t + k * wordWidth c t + 1) * (timeExp c t + 1) * (d + 1) * 2 ^ timeExp c t := hF
    _ ≤ C * (P * L) * (P * L) * ((A + 1) * (P * L) ^ B) * (a * t) := by gcongr
    _ = C * (P * P) * ((A + 1) * P ^ B) * a * t * L ^ (2 + B) := by rw [pow_add, mul_pow]; ring

/-- **Conditional neighbor count.** A bound
`c_N ≤ C·(log T_n + k w_n + 1)` implies `c_N ≤ K·logScale t`. -/
theorem neighbor_instantiation (C k c : ℕ) (hc : 1 ≤ c) :
    ∃ K : ℕ, ∀ t cN : ℕ, 1 ≤ t → cN ≤ C * (timeExp c t + k * wordWidth c t + 1) → cN ≤ K * logScale t := by
  set a := 2 * c * (7 + 2 * c)
  set P := a + 2 * k * c + 2 * k + 2 * c + 3
  refine ⟨C * P, fun t cN ht hN => ?_⟩
  obtain ⟨hL1, hLc, -, -⟩ := logScale_facts t
  have hτ : timeExp c t ≤ logScale t + a := timeExp_le c t hc ht
  have hw : wordWidth c t < 2 * (logScale t + c) := by
    have := wordWidth_lt c t hc; omega
  have haL : a ≤ a * logScale t := Nat.le_mul_of_pos_right a hL1
  have hkcL : 2 * k * c ≤ 2 * k * c * logScale t := Nat.le_mul_of_pos_right _ hL1
  have hPL : P * logScale t = a * logScale t + 2 * k * c * logScale t + 2 * k * logScale t +
      2 * c * logScale t + 3 * logScale t := by
    simp only [P]; ring
  have : timeExp c t + k * wordWidth c t + 1 ≤ P * logScale t := by
    have : k * wordWidth c t ≤ k * (2 * (logScale t + c)) := Nat.mul_le_mul_left _ hw.le
    have e : k * (2 * (logScale t + c)) = 2 * k * logScale t + 2 * k * c := by ring
    omega
  calc cN ≤ C * (timeExp c t + k * wordWidth c t + 1) := hN
    _ ≤ C * (P * logScale t) := Nat.mul_le_mul_left _ this
    _ = C * P * logScale t := by ring

/-- Padding facts for the bounded RAM instance: `τ = log T_n ≥ 1`,
`2 ≤ |x̄| ≤ 2^τ`, and `|x̄|` is a power of two. -/
theorem instance_side_conditions (c n t : ℕ) (hc : 16 ≤ c) (hn : 1 ≤ n) (hnt : n ≤ t) :
    1 ≤ timeExp c t ∧ 2 ≤ inputPadLength c n t ∧ inputPadLength c n t ≤ 2 ^ timeExp c t ∧
      inputPadLength c n t = 2 ^ Nat.log 2 (inputPadLength c n t) := by
  obtain ⟨h1, -, h3, h4⟩ := inputPad_facts c n t hc hn hnt
  have hs := padTime_shape c t hc (by omega)
  refine ⟨by omega, by omega, by unfold padTime at h4; omega, ?_⟩
  unfold inputPadLength
  rw [Nat.log_pow (by norm_num)]

end NearCubicGates.Adapters.ShortPCP

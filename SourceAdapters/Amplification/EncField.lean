import Proof.Wire_3_5.Shared.GF
import Mathlib

/-!
# Field arithmetic of the X3 field on numbers (for the encoder machine, X9)

`app:sources`, "Full-range amplification interface" (the rounded STV code over a binary extension field) and proof of `lem:small-bias` ("identify `𝔽_{2^m}` with
`𝔽₂^m`"): elements of `F = 𝔽₂[X]/(p)` are the numbers `a < 2^t`, read through `GF.rep p a` (the released
`Proof/Wire_3_5/Shared/GF.lean`). This module gives the arithmetic the encoder machine performs, as plain recursions
on numbers, with their meaning in `F`:

* `fmul`: shift-and-add multiplication (bits of the second factor low first, `GF.lfsr` = multiplication by `X`);
  `rep_fmul`;
* `fpow`: repeated multiplication; `finv a = a^(2^t − 2)`, the inverse of a nonzero element (`rep_finv`);
* `prodFold`: a running product over `0 … N−1`, skipping one index (`rep_prodFold`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification.Enc

open Polynomial Finset NearCubicWires.WireExponent3_5

/-! ## Numbers below `2^t` -/

theorem mod_two_pow_succ (b s : ℕ) : b % 2 ^ (s + 1) = b % 2 + 2 * (b / 2 % 2 ^ s) := by
  rw [pow_succ', Nat.mod_mul]

theorem toPoly_bit_add (a y : ℕ) (ha : a < 2) : GF.toPoly (a + 2 * y) = GF.toPoly a + X * GF.toPoly y := by
  rw [← GF.toPoly_two_mul]
  interval_cases a
  · simp
  · have e : 1 + 2 * y = 1 ^^^ 2 * y := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor]
      cases i with
      | zero => simp [Nat.testBit_zero]
      | succ i =>
        rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        have h1 : (1 + 2 * y) / 2 = y := by omega
        have h2 : 2 * y / 2 = y := by omega
        rw [h1, h2]; simp
    rw [e, GF.toPoly_xor]

theorem rep_bit_add (p a y : ℕ) (ha : a < 2) : GF.rep p (a + 2 * y) = GF.rep p a + GF.xRoot p * GF.rep p y := by
  simp only [GF.rep, toPoly_bit_add a y ha, map_add, map_mul, AdjoinRoot.mk_X]

/-! ## Multiplication -/

/-- Shift-and-add: `s` rounds of "if the low bit of `b` is set, add `x`; multiply `x` by `X`; halve `b`". -/
def fmulGo (p t : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, r, _, _ => r
  | s + 1, r, x, b => fmulGo p t s (if b % 2 = 1 then r ^^^ x else r) (GF2.lfsr p t x) (b / 2)

/-- The product of `a` and `b` in `𝔽₂[X]/(p)`. -/
def fmul (p t a b : ℕ) : ℕ := fmulGo p t t 0 a b

theorem fmulGo_spec (p t : ℕ) (hp : GF.ModulusOk p t) :
    ∀ (s r x b : ℕ), r < 2 ^ t → x < 2 ^ t →
      fmulGo p t s r x b < 2 ^ t ∧
        GF.rep p (fmulGo p t s r x b) = GF.rep p r + GF.rep p x * GF.rep p (b % 2 ^ s) := by
  intro s
  induction s with
  | zero => intro r x b hr _; simp [fmulGo, hr, Nat.mod_one]
  | succ s ih =>
    intro r x b hr hx
    obtain ⟨hl1, hl2⟩ := GF.lfsr_spec p t x hp hx
    have hr' : (if b % 2 = 1 then r ^^^ x else r) < 2 ^ t := by
      split_ifs
      · exact Nat.xor_lt_two_pow hr hx
      · exact hr
    obtain ⟨h1, h2⟩ := ih _ _ (b / 2) hr' hl1
    simp only [fmulGo]
    refine ⟨h1, ?_⟩
    rw [h2, hl2, mod_two_pow_succ, rep_bit_add p _ _ (Nat.mod_lt _ (by norm_num))]
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
    · rw [if_neg (by omega), hb]; simp; ring
    · rw [if_pos hb, hb, GF.rep_xor]; simp; ring

theorem fmul_spec (p t a b : ℕ) (hp : GF.ModulusOk p t) (ha : a < 2 ^ t) (hb : b < 2 ^ t) :
    fmul p t a b < 2 ^ t ∧ GF.rep p (fmul p t a b) = GF.rep p a * GF.rep p b := by
  obtain ⟨h1, h2⟩ := fmulGo_spec p t hp t 0 a b (Nat.two_pow_pos t) ha
  refine ⟨h1, ?_⟩
  unfold fmul
  rw [h2, Nat.mod_eq_of_lt hb]; simp

/-! ## Powers and inverses -/

/-- `fpow j y a = y·a^j`. -/
def fpow (p t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, y, _ => y
  | j + 1, y, a => fpow p t j (fmul p t y a) a

theorem fpow_spec (p t : ℕ) (hp : GF.ModulusOk p t) (a : ℕ) (ha : a < 2 ^ t) :
    ∀ (j y : ℕ), y < 2 ^ t → fpow p t j y a < 2 ^ t ∧ GF.rep p (fpow p t j y a) = GF.rep p y * GF.rep p a ^ j := by
  intro j
  induction j with
  | zero => intro y hy; simp [fpow, hy]
  | succ j ih =>
    intro y hy
    obtain ⟨h1, h2⟩ := fmul_spec p t y a hp hy ha
    obtain ⟨h3, h4⟩ := ih _ h1
    refine ⟨h3, ?_⟩
    simp only [fpow]
    rw [h4, h2]; ring

/-- The inverse `a^(2^t − 2)`. -/
def finv (p t a : ℕ) : ℕ := fpow p t (2 ^ t - 2) 1 a

theorem finv_spec (p t : ℕ) (hc : GF.PrimitiveCert p t) (a : ℕ) (ha : a < 2 ^ t) (h0 : GF.rep p a ≠ 0) :
    finv p t a < 2 ^ t ∧
      @Eq (AdjoinRoot (GF.toPoly p)) (GF.rep p (finv p t a))
        (letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p t hc⟩; (GF.rep p a)⁻¹) := by
  letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p t hc⟩
  have h1 : 1 < 2 ^ t := Nat.one_lt_two_pow (by have := hc.1; omega)
  obtain ⟨hl, hr⟩ := fpow_spec p t hc.2.1 a ha (2 ^ t - 2) 1 h1
  refine ⟨hl, ?_⟩
  unfold finv
  rw [hr, GF.rep, GF.toPoly_one, map_one, one_mul]
  · have hcard : Nat.card (AdjoinRoot (GF.toPoly p)) = 2 ^ t := GF.natCard_ref p t hc.2.1
    haveI : Finite (AdjoinRoot (GF.toPoly p)) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    have hu := pow_card_eq_one' (G := (AdjoinRoot (GF.toPoly p))ˣ) (x := Units.mk0 _ h0)
    rw [Nat.card_units, hcard] at hu
    have hu' : GF.rep p a ^ (2 ^ t - 1) = 1 := by
      have := congrArg Units.val hu
      simpa using this
    have e : 2 ^ t - 1 = (2 ^ t - 2) + 1 := by omega
    rw [e, pow_succ] at hu'
    exact (eq_inv_of_mul_eq_one_left hu')

/-! ## Running products skipping one index -/

/-- `∏_{w < N, w ≠ v} f w` as a fold of `fmul`, from the start value `y`. -/
def prodFold (p t : ℕ) (f : ℕ → ℕ) (v N y : ℕ) : ℕ :=
  (List.range N).foldl (fun acc w => if w = v then acc else fmul p t acc (f w)) y

theorem prodFold_succ (p t : ℕ) (f : ℕ → ℕ) (v N y : ℕ) :
    prodFold p t f v (N + 1) y = if N = v then prodFold p t f v N y else fmul p t (prodFold p t f v N y) (f N) := by
  simp [prodFold, List.range_succ, List.foldl_append]

theorem prodFold_zero (p t : ℕ) (f : ℕ → ℕ) (v y : ℕ) : prodFold p t f v 0 y = y := rfl

theorem prodFold_spec (p t : ℕ) (hp : GF.ModulusOk p t) (f : ℕ → ℕ) (v : ℕ) :
    ∀ (N y : ℕ), (∀ w < N, f w < 2 ^ t) → y < 2 ^ t → prodFold p t f v N y < 2 ^ t ∧
      GF.rep p (prodFold p t f v N y) = GF.rep p y * ∏ w ∈ (range N).erase v, GF.rep p (f w) := by
  intro N
  induction N with
  | zero => intro y _ hy; simp [prodFold, hy]
  | succ N ih =>
    intro y hf hy
    obtain ⟨h1, h2⟩ := ih y (fun w hw => hf w (by omega)) hy
    have e : prodFold p t f v (N + 1) y =
        (if N = v then prodFold p t f v N y else fmul p t (prodFold p t f v N y) (f N)) := by
      simp [prodFold, List.range_succ, List.foldl_append]
    rw [e]
    by_cases hN : N = v
    · rw [if_pos hN]
      refine ⟨h1, ?_⟩
      rw [h2]
      congr 1
      rw [Finset.range_add_one, hN, erase_insert (by simp), erase_eq_of_notMem (by simp)]
    · rw [if_neg hN]
      obtain ⟨h3, h4⟩ := fmul_spec p t _ _ hp h1 (hf N (by omega))
      refine ⟨h3, ?_⟩
      rw [h4, h2, Finset.range_add_one, Finset.erase_insert_of_ne hN, prod_insert (by simp)]
      ring

end NearCubicGates.Adapters.Amplification.Enc

import SourceAdapters.ShortPCP.Field6
import Proof.Wire_3_5.GFExists

/-!
# The mask machine's reference layer: the multiset `S` at word level

 (Step 3 of `thm:short-pcp-ours`): "Choose the least nonnegative integer `m` such that
`2^{2m} ≥ r0² n K1 f^{b1}`, and use the powering construction in the proof of `lem:small-bias` over `𝔽_{2^m}` …
Choosing `m` uses only integer comparisons; constructing the field and listing the multiset also take
`poly(n, log T)` time." (proof of `lem:small-bias`): "Find an irreducible polynomial of degree `m`
over `𝔽₂` by exhaustive search … For `a, b ∈ 𝔽_{2^m}` let `σ_{a,b} ∈ {0,1}^r` have coordinates `a^j·b`".

This module states what the mask machine (`OracleCircuitPCP.MaskMachine`) computes, in the words a machine holds:
- `mDeg_eq_clog`: the `m` of proof of `thm:short-pcp-ours` is `⌈log₄ N⌉`, found by comparing `N` with `4^0, 4^1, …`;
- `bdot_rep`: the inner product `u·v` of field elements given by `m`-bit words `x, y` is the parity of `x AND y`
  (`wordDot`), for every modulus of degree `m`;
- `sigma_eq_words`: `σ_{a,b}` is `(wordDot m (w j) b)_{j<r}` for ANY words `w j < 2^m` with `rep (w j) = rep(a)^j`
  — exactly what iterating the field product `GF.fmulShift` from `w 0 = 1` produces (`rep p z = rep p x · rep p y`,
  `z < 2^m`);
- `firstPrimitive_ok`: the exhaustive search's result (`Joins/BinaryFieldArithmetic.lean`) is a modulus of degree `m`
  (for `m ≥ 1`);
- `randEq_step`: `r0 = max(rand_{RS,=}(f), f)` through the recursion (27) of BCGT13 Lemma C.9 as a table indexed
  by `κ ≤ f` (each entry from two earlier ones).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.ShortPCP

/-! ## `m` by integer comparisons (proof of `thm:short-pcp-ours`) -/

/-- "the least nonnegative integer `m` such that `2^{2m} ≥ N`" is `⌈log₄ N⌉`. -/
theorem mDeg_eq_clog (N : ℕ) : Amplified.mDeg N = Nat.clog 4 N := by
  apply le_antisymm
  · apply Nat.find_min' (Amplified.exists_pow N)
    rw [pow_mul]
    exact Nat.le_pow_clog (by norm_num) N
  · apply Nat.clog_le_of_le_pow
    have h := Nat.find_spec (Amplified.exists_pow N)
    rw [pow_mul] at h
    exact h

/-- The comparison loop: `m` is the least with `N ≤ 4^m`. -/
theorem mDeg_spec (N : ℕ) : N ≤ 4 ^ Amplified.mDeg N ∧ ∀ k < Amplified.mDeg N, 4 ^ k < N := by
  rw [mDeg_eq_clog]
  refine ⟨Nat.le_pow_clog (by norm_num) N, fun k hk => ?_⟩
  by_contra h
  exact absurd (Nat.clog_le_of_le_pow (not_lt.mp h)) (not_le.mpr hk)

/-! ## The inner product of words (proof of `lem:small-bias`) -/

/-- The bit inner product of two `m`-bit words: the parity of their common ones. -/
def wordDot (m x y : ℕ) : Bool := decide ((∑ i : Fin m, (x.testBit i && y.testBit i).toNat) % 2 = 1)

theorem natCast_eq_one_iff_mod (k : ℕ) : ((k : ZMod 2) = 1) ↔ k % 2 = 1 := by
  rw [← ZMod.val_natCast_of_lt (show 1 < 2 by norm_num), ← ZMod.val_natCast]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact ZMod.val_injective _ (by rw [h]; rfl)

theorem bitF_mul (a b : Bool) : GF.bitF a * GF.bitF b = (((a && b).toNat : ℕ) : ZMod 2) := by
  cases a <;> cases b <;> rfl

/-- **`u·v` on words**: for a modulus of degree `m` and words `x, y < 2^m`, `rep x · rep y` (the inner product of the
masks, proof of `lem:small-bias`) is the parity of `x AND y`. -/
theorem bdot_rep {p m : ℕ} (hp : GF.ModulusOk p m) {x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    Amplified.bdot p m (GF.rep p x) (GF.rep p y) = wordDot m x y := by
  unfold Amplified.bdot Amplified.dotZ wordDot
  rw [Verifier.maskOf_rep hp x hx, Verifier.maskOf_rep hp y hy]
  simp only [bitF_mul]
  rw [← Nat.cast_sum]
  simp only [natCast_eq_one_iff_mod]

/-- The exhaustive search (proof of `lem:small-bias`) returns a modulus of degree `m` (`m ≥ 1`). -/
theorem firstPrimitive_ok {m : ℕ} (hm : 1 ≤ m) : GF.ModulusOk (Amplified.modulus m) m :=
  (GF.firstPrimitive_cert m hm).2.1

/-- **`σ_{a,b}` from power words** (proof of `lem:small-bias`): if `w j < 2^m` and `rep (w j) = rep(a)^j` for `j < r` (iterated
field multiplication from `w 0 = 1`), then `σ_{a,b} = (wordDot m (w j) b)_{j<r}` for `b < 2^m`. -/
theorem sigma_eq_words {m r a b : ℕ} (w : ℕ → ℕ)
    (hw : ∀ j < r, w j < 2 ^ m ∧ GF.rep (Amplified.modulus m) (w j) = GF.rep (Amplified.modulus m) a ^ j)
    (hb : b < 2 ^ m) :
    Amplified.sigma m r a b = List.ofFn fun j : Fin r => wordDot m (w j) b := by
  unfold Amplified.sigma
  congr 1
  funext j
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Amplified.bdot, Amplified.dotZ, wordDot]
  · rw [← (hw j j.isLt).2, bdot_rep (firstPrimitive_ok hm) (hw j j.isLt).1 hb]

/-- The listing order: `a` outer, `b` inner, both over the words `< 2^m` (proof of `thm:short-pcp-ours`: `|S| = 2^{2m}`). -/
theorem masksOf_length (r f n K1 b1 : ℕ) :
    (masksOf r f n K1 b1).length = 2 ^ Amplified.mDeg (r ^ 2 * n * K1 * f ^ b1) *
      2 ^ Amplified.mDeg (r ^ 2 * n * K1 * f ^ b1) := by
  simp [masksOf, List.length_flatMap, List.sum_replicate]

theorem mem_masksOf_length {r f n K1 b1 : ℕ} {σ : List Bool} (h : σ ∈ masksOf r f n K1 b1) : σ.length = r := by
  simp only [masksOf, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a, -, b, -, rfl⟩ := h
  simp [Amplified.sigma]

/-! ## `r0 = max(rand_{RS,=}(f), f)` as a table (BCGT13 Lemma C.9, recursion (27)) -/

/-- One step of recursion (27) for the tuple `(η, κ0, γ, μ) = (2, 4, 0, 1)`, from a table `t` of earlier values:
`r(κ) = 0` for `κ ≤ 4`, else `1 + max{⌈κ/2⌉ + r(⌊κ/2⌋ + 2), ⌊κ/2⌋ + 1 + r(⌈κ/2⌉)}`. -/
def randStep (t : ℕ → ℕ) (κ : ℕ) : ℕ :=
  if κ ≤ 4 then 0 else 1 + max ((κ + 1) / 2 + t (κ / 2 + 2)) (κ / 2 + 1 + t ((κ + 1) / 2))

theorem randEqF_succ (n κ : ℕ) :
    NearCubicGates.Published.BCGT13.randEqF tuple0 (n + 1) κ =
      randStep (NearCubicGates.Published.BCGT13.randEqF tuple0 n) κ := by
  simp only [NearCubicGates.Published.BCGT13.randEqF, randStep, tuple0, Nat.sub_zero, add_zero, add_assoc,
    Nat.reduceAdd]

/-- The fuel of recursion (27) is irrelevant once it exceeds the argument. -/
theorem randEqF_fuel (n κ : ℕ) (h : κ ≤ n) :
    NearCubicGates.Published.BCGT13.randEqF tuple0 (n + 1) κ =
      NearCubicGates.Published.BCGT13.randEqF tuple0 n κ := by
  induction n generalizing κ with
  | zero =>
    obtain rfl : κ = 0 := by omega
    rw [randEqF_succ]; simp [randStep, NearCubicGates.Published.BCGT13.randEqF]
  | succ n ih =>
    rw [randEqF_succ, randEqF_succ]
    unfold randStep
    split_ifs with h4
    · rfl
    · rw [ih (κ / 2 + 2) (by omega), ih ((κ + 1) / 2) (by omega)]

theorem randEqF_stable (k n : ℕ) (hk : k ≤ n) :
    NearCubicGates.Published.BCGT13.randEqF tuple0 n k = NearCubicGates.Published.BCGT13.randEqF tuple0 k k := by
  induction n, hk using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [randEqF_fuel n k hkn, ih]

/-- **The table form**: `rand_{RS,=}(κ) = randStep (rand_{RS,=}) κ` with both arguments `< κ` when `κ > 4`, so a
machine fills the table `κ = 0, 1, …, f` with one step per entry. -/
theorem randEq_step (κ : ℕ) :
    NearCubicGates.Published.BCGT13.randEq tuple0 κ = randStep (NearCubicGates.Published.BCGT13.randEq tuple0) κ := by
  cases κ with
  | zero => simp [NearCubicGates.Published.BCGT13.randEq, NearCubicGates.Published.BCGT13.randEqF, randStep]
  | succ n =>
    unfold NearCubicGates.Published.BCGT13.randEq
    rw [randEqF_succ]
    unfold randStep
    split_ifs with h4
    · rfl
    · rw [randEqF_stable ((n + 1) / 2 + 2) n (by omega), randEqF_stable ((n + 1 + 1) / 2) n (by omega)]

end NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

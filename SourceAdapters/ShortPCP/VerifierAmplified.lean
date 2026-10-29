import SourceAdapters.ShortPCP.VerifierJoin
import SourceAdapters.ShortPCP.SmallBias
import SourceAdapters.Field.BinaryField

/-!
# The amplified verifier on an affine constraint instance, from BCGT13 Theorem 11.1

`amplifiedVerifier : BCGT13_Theorem11_1 → Joins.AmplifiedVerifier` (proof of `thm:short-pcp-ours`,
Step 3, with `lem:small-bias` and `lem:patch-r`).

- The inner product of `m`-bit words over `𝔽_{2^m}` (`Amplified.bdot`) is additive in its first argument and balanced,
  so the powering multiset is `r/2^m`-biased (`smallBias_bias`, `lem:small-bias`(i), through `powering_bias`).
- `patch_sound` is `lem:patch-r`(iii) (from `hitting`, `lem:small-bias`(ii)); completeness is `lem:patch-r`(ii).
- The field is that of `Joins/BinaryFieldArithmetic.lean`: `GF.firstPrimitive m` is a primitive, hence irreducible,
  modulus (`binaryFieldArithmetic`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Verifier

open Finset NearCubicWires.WireExponent3_5 NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP
open NearCubicGates.Adapters.ACSP.Affine NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.Joins.SingleRun.Amplified NearCubicGates.Adapters.ShortPCP.SmallBias

/-! ## The inner product of `m`-bit words (`lem:small-bias`) -/

section InnerProduct

variable {p m : ℕ}

theorem maskOf_lt (u : AdjoinRoot (GF.toPoly p)) : maskOf p m u < 2 ^ m := by
  unfold maskOf
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact Nat.two_pow_pos _

theorem dotZ_comm (u v : AdjoinRoot (GF.toPoly p)) : dotZ p m u v = dotZ p m v u := by
  unfold dotZ; apply sum_congr rfl; intro i _; ring

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

variable (hp : GF.ModulusOk p m)
include hp

theorem rep_maskOf (u : AdjoinRoot (GF.toPoly p)) : GF.rep p (maskOf p m u) = u := by
  unfold maskOf
  have hex : ∃ a, a < 2 ^ m ∧ GF.rep p a = u := GF.rep_surj p m hp u
  rw [dif_pos hex]
  exact (Nat.find_spec hex).2

theorem maskOf_rep (a : ℕ) (ha : a < 2 ^ m) : maskOf p m (GF.rep p a) = a :=
  GF.rep_injOn p m _ _ hp (maskOf_lt _) ha (rep_maskOf hp _)

theorem maskOf_add (u v : AdjoinRoot (GF.toPoly p)) : maskOf p m (u + v) = maskOf p m u ^^^ maskOf p m v := by
  conv_lhs => rw [← rep_maskOf hp u, ← rep_maskOf hp v, ← GF.rep_xor]
  exact maskOf_rep hp _ (Nat.xor_lt_two_pow (maskOf_lt _) (maskOf_lt _))

theorem dotZ_add_left (u v w : AdjoinRoot (GF.toPoly p)) :
    dotZ p m (u + v) w = dotZ p m u w + dotZ p m v w := by
  unfold dotZ
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl; intro i _
  rw [maskOf_add hp, Nat.testBit_xor, GF.bitF_add]; ring

theorem bdot_add (u v w : AdjoinRoot (GF.toPoly p)) :
    bdot p m (u + v) w = xor (bdot p m u w) (bdot p m v w) := by
  unfold bdot
  rw [dotZ_add_left hp]
  rcases zmod2_cases (dotZ p m u w) with h1 | h1 <;> rcases zmod2_cases (dotZ p m v w) with h2 | h2 <;>
    simp [h1, h2]

theorem bdot_balanced [Fintype (AdjoinRoot (GF.toPoly p))] (u : AdjoinRoot (GF.toPoly p)) (hu : u ≠ 0) :
    ∑ w, sgn (bdot p m u w) = 0 := by
  have hm0 : maskOf p m u ≠ 0 := by
    intro h; apply hu; rw [← rep_maskOf hp u, h, GF.rep_zero]
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hm0
  have him : i < m := by
    by_contra hc
    have := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (maskOf_lt (p := p) (m := m) u)
      (Nat.pow_le_pow_right (n := 2) (by norm_num) (show m ≤ i by omega)))
    rw [this] at hi; exact absurd hi (by simp)
  set e := GF.rep p (2 ^ i)
  have he : bdot p m u e = true := by
    have hme : maskOf p m e = 2 ^ i := maskOf_rep hp _ (Nat.pow_lt_pow_right (by norm_num) him)
    unfold bdot dotZ
    rw [hme]
    simp only [Nat.testBit_two_pow]
    rw [Finset.sum_eq_single ⟨i, him⟩]
    · simp [hi, GF.bitF]
    · intro k _ hk; simp [GF.bitF, show ¬ (i = k.val) from fun h => hk (Fin.ext h.symm)]
    · simp
  have hshift : ∑ w, sgn (bdot p m u w) = ∑ w, sgn (bdot p m u (w + e)) :=
    (Equiv.sum_comp (Equiv.addRight e) (fun w => sgn (bdot p m u w))).symm
  have hflip : ∀ w, bdot p m u (w + e) = xor (bdot p m u w) true := by
    intro w
    unfold bdot
    rw [dotZ_comm, dotZ_add_left hp, dotZ_comm w, dotZ_comm e]
    have : dotZ p m u e = 1 := by unfold bdot at he; simpa using he
    rw [this]
    rcases zmod2_cases (dotZ p m u w) with h1 | h1 <;> simp [h1]
  simp only [hflip, sgn_xor] at hshift
  have : sgn true = -1 := by simp [sgn]
  rw [this] at hshift
  simp only [mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  linarith

/-- **`lem:small-bias`(i)**: the powering multiset over `𝔽_{2^m}` is `r/2^m`-biased. -/
theorem smallBias_bias [Fintype (AdjoinRoot (GF.toPoly p))] [DecidableEq (AdjoinRoot (GF.toPoly p))]
    [Fact (Irreducible (GF.toPoly p))] (hcard : Fintype.card (AdjoinRoot (GF.toPoly p)) = 2 ^ m)
    (r : ℕ) (α : Fin r → Bool) (hα : α ≠ fun _ => false) :
    |(∑ ab : AdjoinRoot (GF.toPoly p) × AdjoinRoot (GF.toPoly p), chi α (powVec (bdot p m) r ab)) /
      (Fintype.card (AdjoinRoot (GF.toPoly p) × AdjoinRoot (GF.toPoly p)) : ℝ)| ≤ r / 2 ^ m := by
  have := powering_bias (bdot p m) (bdot_add hp) (bdot_balanced hp) r α hα
  rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at this

end InnerProduct

/-! ## `lem:patch-r` -/

/-- **`lem:patch-r`(iii)**. -/
theorem patch_sound {r : ℕ} {ι : Type} [Fintype ι] [Nonempty ι] (σ : ι → (Fin r → Bool)) (ε s σ0 : ℝ)
    (hbias : ∀ α : Fin r → Bool, α ≠ (fun _ => false) → |(∑ i, chi α (σ i)) / (Fintype.card ι : ℝ)| ≤ ε)
    (hσ0 : 0 < σ0) (hεs : ε ^ 2 ≤ s * σ0) (V0 : (Fin r → Bool) → Bool) (hrej : acceptFrac V0 ≤ 1 - σ0) :
    acceptFrac (fun R => decide (∀ i, V0 (vxor R (σ i)) = true)) ≤ s := by
  classical
  set B := univ.filter fun R : Fin r → Bool => V0 R = false with hBdef
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin r → Bool))) (fun R => V0 R = true)
  have hcardu : ((univ : Finset (Fin r → Bool)).card : ℝ) = 2 ^ r := by simp
  have hBcard : (B.card : ℝ) = 2 ^ r - (univ.filter fun R => V0 R = true).card := by
    have : B = univ.filter fun R => ¬ (V0 R = true) := by rw [hBdef]; congr; funext R; simp
    rw [this]
    have h := congrArg (fun k : ℕ => (k : ℝ)) hsplit
    simp only [Nat.cast_add] at h
    rw [← hcardu]; linarith
  have hμ : σ0 ≤ (B.card : ℝ) / 2 ^ r := by
    unfold acceptFrac at hrej
    rw [hBcard, sub_div, div_self h2r.ne']
    linarith
  have hBne : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hμ; simp at hμ; linarith
  have hhit := hitting σ ε hbias B hBne
  have hfilt : (univ.filter fun R => decide (∀ i, V0 (vxor R (σ i)) = true) = true) =
      univ.filter fun R => ∀ i, vxor R (σ i) ∉ B := by
    congr; funext R; simp [hBdef]
  unfold acceptFrac
  rw [hfilt]
  refine hhit.trans ?_
  have hμpos : 0 < (B.card : ℝ) / 2 ^ r := lt_of_lt_of_le hσ0 hμ
  rw [div_le_iff₀ hμpos]
  calc ε ^ 2 ≤ s * σ0 := hεs
    _ ≤ s * ((B.card : ℝ) / 2 ^ r) := by
      apply mul_le_mul_of_nonneg_left hμ
      by_contra hs; push Not at hs; nlinarith [sq_nonneg ε]

theorem sigma_getD {p m : ℕ} (hpm : p = modulus m) (r a b : ℕ) [Fact (Irreducible (GF.toPoly p))] (i : Fin r) :
    (sigma m r a b).getD i.val false = powVec (bdot p m) r (GF.rep p a, GF.rep p b) i := by
  subst hpm
  simp only [sigma, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
  rfl

/-! ## `V1` is the patched conjunction of `V0` -/

section Patched

variable {Kc : ℕ} {c : Instance} {xs : List Bool}

/-- The verdict does not depend on the mask list of the request. -/
theorem runVerdict_request [Fact (Irreducible c.irrPoly)] [DecidableEq c.Fld] (S : List (List Bool))
    (π ρ : ℕ → Bool) :
    (request c xs S).runVerdict (RingHom.id c.Fld) ((request c xs S).decode (RingHom.id c.Fld) π) ρ =
      (request c xs [[]]).runVerdict (RingHom.id c.Fld) ((request c xs [[]]).decode (RingHom.id c.Fld) π) ρ := rfl

/-- `V1` on `R` is the conjunction over the masks of `V0` on `R ⊕ σ` (`lem:patch-r`). -/
theorem amplified_all (hG : SingleRun.Good Kc c xs) (n K1 b1 : ℕ) (π : ℕ → Bool) (R : List Bool) :
    Amplified.accepts c xs n K1 b1 π R =
      (masks c n K1 b1).all fun σ =>
        SingleRun.accepts c xs π (List.ofFn fun i : Fin (r0 c) => Request.maskedCoins R σ i.val) := by
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  rw [amplified_eq hG]
  unfold Request.patchedVerdict
  show (masks c n K1 b1).all _ = _
  congr 1
  funext σ
  rw [runVerdict_request, accepts_eq hG]
  apply runVerdict_coins
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

end Patched

/-! ## The multiset `S` (Step 3) -/

/-- "the least nonnegative integer `m` such that `2^{2m} ≥ N`", for `N ≥ 2`: `m ≥ 1` and, by minimality,
`2^{2m} < 4N`. -/
theorem mDeg_facts (N : ℕ) (hN2 : 2 ≤ N) :
    1 ≤ mDeg N ∧ N ≤ 2 ^ (2 * mDeg N) ∧ 2 ^ mDeg N * 2 ^ mDeg N < 4 * N := by
  have hmspec : N ≤ 2 ^ (2 * mDeg N) := Nat.find_spec (exists_pow N)
  have hm1 : 1 ≤ mDeg N := by
    by_contra h0
    have : mDeg N = 0 := by omega
    rw [this] at hmspec; simp at hmspec; omega
  have hmin : ¬ (N ≤ 2 ^ (2 * (mDeg N - 1))) := Nat.find_min (exists_pow N) (show mDeg N - 1 < mDeg N by omega)
  refine ⟨hm1, hmspec, ?_⟩
  have : 2 ^ mDeg N * 2 ^ mDeg N = 4 * 2 ^ (2 * (mDeg N - 1)) := by
    rw [← pow_add, show mDeg N + mDeg N = 2 + 2 * (mDeg N - 1) by omega, pow_add]; norm_num
  omega

/-- Step 3: "`|S| = 2^{2m} < 4 r_0^2 n K_1 f^{b_1}`". -/
theorem masks_length (c : Instance) (n K1 b1 : ℕ) (hN2 : 2 ≤ target c n K1 b1) :
    (masks c n K1 b1).length < 4 * target c n K1 b1 := by
  have h := (mDeg_facts _ hN2).2.2
  unfold masks
  simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const', List.sum_replicate,
    smul_eq_mul]
  exact h

/-- Each mask has `r_0` bits. -/
theorem masks_mem_length (c : Instance) (n K1 b1 : ℕ) : ∀ σ ∈ masks c n K1 b1, σ.length = r0 c := by
  intro σ hσ
  unfold masks at hσ
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hσ
  obtain ⟨a, -, b, -, rfl⟩ := hσ
  simp [sigma]

/-- `V1` on `R ∈ {0,1}^{r_0}` is the shifted conjunction of `V0` over `𝔽_{2^m} × 𝔽_{2^m}` (`lem:patch-r`). -/
theorem amplified_shift {Kc : ℕ} {c : Instance} {xs : List Bool} (hG : SingleRun.Good Kc c xs)
    (n K1 b1 : ℕ) (hp : GF.ModulusOk (modulus (mDeg (target c n K1 b1))) (mDeg (target c n K1 b1)))
    [Fact (Irreducible (GF.toPoly (modulus (mDeg (target c n K1 b1)))))]
    [Fintype (AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1)))))]
    [DecidableEq (AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1)))))] (π : ℕ → Bool) (R : Fin (r0 c) → Bool) :
    Amplified.accepts c xs n K1 b1 π (List.ofFn R) =
      decide (∀ uv : AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1)))) ×
          AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1)))),
        SingleRun.accepts c xs π (List.ofFn (vxor R (powVec (bdot (modulus (mDeg (target c n K1 b1)))
          (mDeg (target c n K1 b1))) (r0 c) uv))) = true) := by
  have hfun : ∀ a b, (List.ofFn fun i : Fin (r0 c) =>
      Request.maskedCoins (List.ofFn R) (sigma (mDeg (target c n K1 b1)) (r0 c) a b) i.val) =
      List.ofFn (vxor R (powVec (bdot (modulus (mDeg (target c n K1 b1))) (mDeg (target c n K1 b1))) (r0 c)
        (GF.rep (modulus (mDeg (target c n K1 b1))) a, GF.rep (modulus (mDeg (target c n K1 b1))) b))) := by
    intro a b
    congr 1
    funext i
    rw [Request.maskedCoins, getD_ofFn, sigma_getD rfl]
    rfl
  rw [amplified_all hG]
  unfold masks
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro h ⟨u, v⟩
    obtain ⟨a, ha, rfl⟩ := GF.rep_surj _ _ hp u
    obtain ⟨b, hb, rfl⟩ := GF.rep_surj _ _ hp v
    have := h _ ⟨a, ha, b, hb, rfl⟩
    rwa [hfun] at this
  · rintro h σ ⟨a, ha, b, hb, rfl⟩
    rw [hfun]
    exact h _

/-- **Base soundness amplified** (Step 3): with `1/(K_1 f^{b_1})` below the rejection probability of `V0` and `n ≥ 2`,
`V1` accepts every proof with probability at most `1/n`. -/
theorem amplified_sound {Kc : ℕ} {c : Instance} {xs : List Bool} (hG : SingleRun.Good Kc c xs)
    (n K1 b1 : ℕ) (hK1 : 1 ≤ K1) (hn : 2 ≤ n) (hf : 1 ≤ c.f) (hr0 : 1 ≤ r0 c) (π : ℕ → Bool)
    (hs : acceptFrac (fun R : Fin (r0 c) → Bool => SingleRun.accepts c xs π (List.ofFn R)) ≤
      1 - 1 / ((K1 : ℝ) * (c.f : ℝ) ^ b1)) :
    acceptFrac (fun R : Fin (r0 c) → Bool => Amplified.accepts c xs n K1 b1 π (List.ofFn R)) ≤ 1 / (n : ℝ) := by
  have hN2 : 2 ≤ target c n K1 b1 := by
    have e1 : 1 ≤ r0 c ^ 2 := Nat.one_le_pow _ _ hr0
    have e2 : 1 ≤ c.f ^ b1 := Nat.one_le_pow _ _ hf
    unfold target
    have : 2 ≤ r0 c ^ 2 * n := by nlinarith
    have : 2 ≤ r0 c ^ 2 * n * K1 := by nlinarith
    nlinarith
  obtain ⟨hm1, hmspec, -⟩ := mDeg_facts _ hN2
  have hcert := (NearCubicGates.Adapters.Field.binaryFieldArithmetic.2.1 (mDeg (target c n K1 b1)) hm1).1
  have hp : GF.ModulusOk (modulus (mDeg (target c n K1 b1))) (mDeg (target c n K1 b1)) := hcert.2.1
  haveI : Fact (Irreducible (GF.toPoly (modulus (mDeg (target c n K1 b1))))) :=
    ⟨GF.irreducible_ref _ _ hcert⟩
  letI : Fintype (AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1))))) :=
    Fintype.ofEquiv _ (GF.encEquiv _ _ hp)
  letI : DecidableEq (AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1))))) := Classical.decEq _
  have hcardK : Fintype.card (AdjoinRoot (GF.toPoly (modulus (mDeg (target c n K1 b1))))) =
      2 ^ mDeg (target c n K1 b1) := by
    rw [← Nat.card_eq_fintype_card]; exact GF.natCard_ref _ _ hp
  rw [funext (amplified_shift hG n K1 b1 hp π)]
  have hfr : (1 : ℝ) ≤ c.f := by exact_mod_cast hf
  have hK1r : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfb : (1 : ℝ) ≤ (c.f : ℝ) ^ b1 := one_le_pow₀ hfr
  have hσ0 : (0 : ℝ) < 1 / ((K1 : ℝ) * (c.f : ℝ) ^ b1) := by positivity
  have hεs : ((r0 c : ℝ) / 2 ^ mDeg (target c n K1 b1)) ^ 2 ≤ 1 / (n : ℝ) * (1 / ((K1 : ℝ) * (c.f : ℝ) ^ b1)) := by
    have hNr : ((r0 c : ℝ) ^ 2 * n * K1 * (c.f : ℝ) ^ b1) ≤
        (2 : ℝ) ^ mDeg (target c n K1 b1) * 2 ^ mDeg (target c n K1 b1) := by
      have := hmspec
      rw [show 2 * mDeg (target c n K1 b1) = mDeg (target c n K1 b1) + mDeg (target c n K1 b1) by omega,
        pow_add] at this
      unfold target at this
      exact_mod_cast this
    rw [div_pow, one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact patch_sound _ _ _ _ (fun α hα => smallBias_bias hp hcardK (r0 c) α hα) hσ0 hεs
    (fun R : Fin (r0 c) → Bool => SingleRun.accepts c xs π (List.ofFn R)) hs

/-! ## The join -/

/-- **`Joins.AmplifiedVerifier` from BCGT13 Theorem 11.1** (proof of `thm:short-pcp-ours`, Step 3), with the
constants of `singleRunVerifier`. -/
theorem amplifiedVerifier (h11 : BCGT13_Theorem11_1) : AmplifiedVerifier := by
  intro Kc
  refine ⟨120 * max Kc 1, 37, 64, 4, by omega, fun c xs n hG hn => ?_⟩
  obtain ⟨hc, hs⟩ := singleRun_core h11 hG
  obtain ⟨h1, h2, -, h4, h5⟩ := singleRun_resources hG
  have hN2 : 2 ≤ target c n (120 * max Kc 1) 37 := by
    have e1 : 1 ≤ r0 c ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e2 : 1 ≤ c.f ^ 37 := Nat.one_le_pow _ _ (by omega)
    unfold target
    have : 2 ≤ r0 c ^ 2 * n := by nlinarith
    have : 2 ≤ r0 c ^ 2 * n * (120 * max Kc 1) := le_trans this (Nat.le_mul_of_pos_right _ (by omega))
    exact le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨?_, ?_, masks_length c n _ _ hN2, masks_mem_length c n _ _, ?_, ?_, h1, h2, h4, h5⟩
  · intro ha
    obtain ⟨π, hπ⟩ := hc ha
    refine ⟨π, fun R => ?_⟩
    rw [amplified_all hG]
    simp [hπ]
  · intro hna π
    exact amplified_sound hG n _ 37 (by omega) hn h1 (by omega) π (hs hna π)
  · intro π R R' hR
    rw [amplified_all hG, amplified_all hG]
    congr 1
    funext σ
    congr 2
    funext i
    simp only [Request.maskedCoins, hR i.val i.isLt]
  · intro π π' hπ R
    rw [amplified_all hG, amplified_all hG]
    congr 1
    funext σ
    exact accepts_local hG π π' hπ _

end NearCubicGates.Adapters.ShortPCP.Verifier

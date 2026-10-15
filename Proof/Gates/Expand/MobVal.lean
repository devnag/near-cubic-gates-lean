import Proof.Gates.Expand.Mob3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-! ## Bit facts -/

theorem testBit_shift_add (a f W j : ℕ) (hf : f < 2 ^ W) :
    (a * 2 ^ W + f).testBit j = if j < W then f.testBit j else a.testBit (j - W) := by
  rw [mul_comm]; exact Nat.testBit_two_pow_mul_add a hf j

theorem and_shift (a b f W : ℕ) (hf : f < 2 ^ W) : (a * 2 ^ W + f) &&& (b * 2 ^ W) = (a &&& b) * 2 ^ W := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_shift_add a f W j hf, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_and]
  by_cases hj : j < W
  · simp [hj, show ¬ W ≤ j by omega]
  · simp [hj, show W ≤ j by omega]

theorem and_shift' (a b W : ℕ) : (a * 2 ^ W) &&& (b * 2 ^ W) = (a &&& b) * 2 ^ W := by
  simpa using and_shift a b 0 W (Nat.two_pow_pos W)

theorem and_low (a f W : ℕ) (hf : f < 2 ^ W) : (a * 2 ^ W + f) &&& (2 ^ W - 1) = f := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_add_mod_of_lt hf]

theorem mul_two_pow_inj {a b W : ℕ} (h : a * 2 ^ W = b * 2 ^ W) : a = b :=
  Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos W) h

/-- The record of a set of size `d`: the low bits and the parity bit. -/
theorem pk_mask (s d V : ℕ) (hs : s < 2 ^ V) : (s + d * 2 ^ V) &&& (2 ^ V - 1) = s := and_mask_pk s d V hs

theorem pk_par (s d V : ℕ) (hs : s < 2 ^ V) : (s + d * 2 ^ V) &&& 2 ^ V = if d % 2 = 1 then 2 ^ V else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow, show s + d * 2 ^ V = d * 2 ^ V + s by ring, testBit_shift_add d s V j hs]
  by_cases hjV : j = V
  · subst hjV
    simp only [lt_irrefl, if_false, Nat.sub_self, decide_true, Bool.and_true, Nat.testBit_zero]
    split_ifs with h
    · simp [h]
    · simp; omega
  · simp only [decide_eq_false (Ne.symm hjV), Bool.and_false]
    split_ifs <;> simp [Nat.testBit_two_pow, Ne.symm hjV]

/-- `t ⊆ s` as bits. -/
theorem and_eq_iff_subset (V t s : ℕ) (ht : t < 2 ^ V) :
    (t &&& s) = t ↔ setOf V t ⊆ setOf V s := by
  constructor
  · intro h v hv
    simp only [setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have := congrArg (fun x => x.testBit v.val) h
    simp only [Nat.testBit_and] at this
    rw [hv] at this; simpa using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < V
    · by_cases hti : t.testBit i
      · have : (⟨i, hi⟩ : Fin V) ∈ setOf V s := h (by simp [setOf, hti])
        simp only [setOf, Finset.mem_filter, Finset.mem_univ, true_and] at this
        simp [hti, this]
      · simp [hti]
    · have hp : 2 ^ V ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht hp)]

/-! ## One step -/

/-- The signed term of `T` against `S` (as integers). -/
def termZ {V' : ℕ} (F : Formula V') (s dS t dT : ℕ) : ℤ :=
  if setOf V' t ⊆ setOf V' s then (if dT % 2 = dS % 2 then 1 else -1) * (F.eval (boolPoint (ind (setOf V' t))))
  else 0

theorem mobStep_modEq {V' : ℕ} (F : Formula V') (V W s dS t dT acc : ℕ) (hs : s < 2 ^ V) (ht : t < 2 ^ V)
    (ht' : t < 2 ^ V') (hacc : acc < 2 ^ W) :
    mobStep (2 ^ W - 1) ((2 ^ V - 1) * 2 ^ W) (2 ^ V * 2 ^ W) (s * (2 ^ W - 1 + 1))
      (((s + dS * 2 ^ V) &&& 2 ^ V) * (2 ^ W - 1 + 1)) acc ((t + dT * 2 ^ V) * 2 ^ W + (valAlg W t).eval F) < 2 ^ W ∧
    (mobStep (2 ^ W - 1) ((2 ^ V - 1) * 2 ^ W) (2 ^ V * 2 ^ W) (s * (2 ^ W - 1 + 1))
      (((s + dS * 2 ^ V) &&& 2 ^ V) * (2 ^ W - 1 + 1)) acc ((t + dT * 2 ^ V) * 2 ^ W + (valAlg W t).eval F) : ℤ) ≡
      acc + termZ F s dS t dT [ZMOD 2 ^ W] := by
  set v := (t + dT * 2 ^ V) * 2 ^ W + (valAlg W t).eval F with hv
  have hW1 : 2 ^ W - 1 + 1 = 2 ^ W := by have := Nat.two_pow_pos W; omega
  have hf : (valAlg W t).eval F < 2 ^ W := (valAlg W t).eval_lt (valAlg_closed W t) F
  have hfZ : ((valAlg W t).eval F : ℤ) ≡ F.eval (boolPoint (ind (setOf V' t))) [ZMOD 2 ^ W] := by
    unfold Int.ModEq; rw [valAlg_eval, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have e1 : v &&& ((2 ^ V - 1) * 2 ^ W) = t * 2 ^ W := by
    rw [hv, and_shift _ _ _ W hf, pk_mask t dT V ht]
  have e2 : (t * 2 ^ W) &&& (s * (2 ^ W - 1 + 1)) = (t &&& s) * 2 ^ W := by rw [hW1, and_shift']
  have e3 : v &&& (2 ^ V * 2 ^ W) = ((t + dT * 2 ^ V) &&& 2 ^ V) * 2 ^ W := by
    rw [hv, and_shift _ _ _ W hf]
  have e4 : v &&& (2 ^ W - 1) = (valAlg W t).eval F := by
    rw [hv, and_low _ _ W hf]
  have hsub : (t * 2 ^ W = (t &&& s) * 2 ^ W) ↔ setOf V' t ⊆ setOf V' s := by
    rw [← and_eq_iff_subset V' t s ht']
    exact ⟨fun h => (mul_two_pow_inj h).symm, fun h => by rw [h]⟩
  have hpar : (((t + dT * 2 ^ V) &&& 2 ^ V) * 2 ^ W = ((s + dS * 2 ^ V) &&& 2 ^ V) * (2 ^ W - 1 + 1)) ↔
      dT % 2 = dS % 2 := by
    rw [hW1, pk_par t dT V ht, pk_par s dS V hs]
    constructor
    · intro h
      have h' := mul_two_pow_inj h
      split_ifs at h' with h1 h2 h2 <;> first | omega | (have := Nat.two_pow_pos V; omega)
    · intro h
      split_ifs with h1 h2 h2 <;> first | rfl | omega
  have hM : 0 < 2 ^ W := Nat.two_pow_pos W
  simp only [mobStep, e1, e2, e3, e4]
  by_cases hS : setOf V' t ⊆ setOf V' s
  · rw [if_pos (hsub.mpr hS)]
    by_cases hP : dT % 2 = dS % 2
    · rw [if_pos (hpar.mpr hP), Nat.and_two_pow_sub_one_eq_mod]
      refine ⟨Nat.mod_lt _ hM, ?_⟩
      unfold termZ; rw [if_pos hS, if_pos hP, one_mul]
      unfold Int.ModEq; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
      exact Int.ModEq.add_left _ hfZ
    · rw [if_neg (fun h => hP (hpar.mp h)), Nat.and_two_pow_sub_one_eq_mod]
      refine ⟨Nat.mod_lt _ hM, ?_⟩
      unfold termZ; rw [if_pos hS, if_neg hP]
      have hle : (valAlg W t).eval F ≤ 2 ^ W - 1 := by omega
      have h2 : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by push_cast; rfl
      have hN : ((acc + (2 ^ W - 1 - (valAlg W t).eval F + 1) : ℕ) : ℤ) =
          (acc : ℤ) + (2 : ℤ) ^ W - ((valAlg W t).eval F : ℤ) := by
        rw [← h2]; omega
      have hmod : (((acc + (2 ^ W - 1 - (valAlg W t).eval F + 1)) % 2 ^ W : ℕ) : ℤ) ≡
          ((acc + (2 ^ W - 1 - (valAlg W t).eval F + 1) : ℕ) : ℤ) [ZMOD 2 ^ W] := by
        rw [Int.natCast_mod, h2]; exact Int.mod_modEq _ _
      have h0 : ((2 : ℤ) ^ W) ≡ 0 [ZMOD 2 ^ W] := by unfold Int.ModEq; simp
      have h3 := ((Int.ModEq.refl (acc : ℤ)).add h0).sub hfZ
      refine hmod.trans ?_
      rw [hN]
      convert h3 using 1
      ring
  · rw [if_neg (fun h => hS (hsub.mp h))]
    refine ⟨hacc, ?_⟩
    unfold termZ; rw [if_neg hS, add_zero]

/-! ## The fold over the family -/

/-- The family as `(set, size)` pairs. -/
def famPairs (V D : ℕ) : List (ℕ × ℕ) := (List.range (D + 1)).flatMap fun d => (level V d).map fun t => (t, d)

theorem famRecs_eq (V D : ℕ) : famRecs V D = (famPairs V D).map fun p => p.1 + p.2 * 2 ^ V := by
  simp only [famRecs, famPairs, List.map_flatMap, List.map_map]; rfl

theorem famPairs_mem (V D : ℕ) (p : ℕ × ℕ) (hp : p ∈ famPairs V D) : p.1 < 2 ^ V ∧ (setOf V p.1).card = p.2 := by
  simp only [famPairs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨d, _, t, ht, rfl⟩ := hp
  exact level_mem V d t ht

theorem valRec_pk {V W : ℕ} (F : Formula V) (t d : ℕ) (ht : t < 2 ^ V) :
    valRec V W F (t + d * 2 ^ V) = (t + d * 2 ^ V) * 2 ^ W + (valAlg W t).eval F := by
  unfold valRec; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem fold_modEq {V : ℕ} (F : Formula V) (W s dS : ℕ) (hs : s < 2 ^ V) (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, p.1 < 2 ^ V) : ∀ acc, acc < 2 ^ W →
    ((List.foldl (mobStep (2 ^ W - 1) ((2 ^ V - 1) * 2 ^ W) (2 ^ V * 2 ^ W) (s * (2 ^ W - 1 + 1))
        (((s + dS * 2 ^ V) &&& 2 ^ V) * (2 ^ W - 1 + 1))) acc
      (l.map fun p => (p.1 + p.2 * 2 ^ V) * 2 ^ W + (valAlg W p.1).eval F) : ℕ) : ℤ) ≡
      acc + (l.map fun p => termZ F s dS p.1 p.2).sum [ZMOD 2 ^ W] := by
  induction l with
  | nil => intro acc _; simp
  | cons p l ih =>
    intro acc hacc
    have hp := hl p List.mem_cons_self
    have hstep := mobStep_modEq F V W s dS p.1 p.2 acc hs hp hp hacc
    simp only [List.map_cons, List.foldl_cons, List.sum_cons]
    refine (ih (fun q hq => hl q (List.mem_cons_of_mem p hq)) _ hstep.1).trans ?_
    have := hstep.2.add_right ((l.map fun p => termZ F s dS p.1 p.2).sum)
    rw [add_assoc] at this; exact this

theorem accOf_modEq {V : ℕ} (F : Formula V) (W D s dS : ℕ) (hs : s < 2 ^ V) :
    (accOf V W ((famRecs V D).map (valRec V W F)) (s + dS * 2 ^ V) : ℤ) ≡
      ((famPairs V D).map fun p => termZ F s dS p.1 p.2).sum [ZMOD 2 ^ W] := by
  unfold accOf mobAcc
  rw [pk_mask s dS V hs, famRecs_eq, List.map_map]
  have hmap : (famPairs V D).map (valRec V W F ∘ fun p => p.1 + p.2 * 2 ^ V) =
      (famPairs V D).map fun p => (p.1 + p.2 * 2 ^ V) * 2 ^ W + (valAlg W p.1).eval F :=
    List.map_congr_left (fun p hp => valRec_pk F p.1 p.2 (famPairs_mem V D p hp).1)
  rw [hmap]
  have := fold_modEq F W s dS hs (famPairs V D) (fun p hp => (famPairs_mem V D p hp).1) 0 (Nat.two_pow_pos W)
  simpa using this

theorem neg_one_pow_sub (a b : ℕ) (h : b ≤ a) : ((-1 : ℤ) ^ (a - b)) = if b % 2 = a % 2 then 1 else -1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, if_pos (by obtain ⟨m, rfl⟩ := hk; omega)]
  · rw [hk.neg_one_pow, if_neg (by obtain ⟨m, rfl⟩ := hk; omega)]

theorem sum_termZ {V : ℕ} (F : Formula V) (D s : ℕ) (hD : (setOf V s).card ≤ D) :
    ((famPairs V D).map fun p => termZ F s (setOf V s).card p.1 p.2).sum = coeff F.expand (setOf V s) := by
  rw [coeff_eq_fam F D (setOf V s) hD]
  have h1 : (famPairs V D).map (fun p => termZ F s (setOf V s).card p.1 p.2) =
      (fam V D).map (fun t => termZ F s (setOf V s).card t (setOf V t).card) := by
    unfold famPairs fam
    rw [List.map_flatMap, List.map_flatMap]
    congr 1; funext d
    rw [List.map_map]
    exact List.map_congr_left (fun t ht => by simp [(level_mem V d t ht).2])
  rw [h1, famS, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, termZ]
  by_cases hsub : setOf V t ⊆ setOf V s
  · rw [if_pos hsub, if_pos hsub, Finset.card_sdiff_of_subset hsub, neg_one_pow_sub _ _ (Finset.card_le_card hsub)]
  · rw [if_neg hsub, if_neg hsub]

/-- **The accumulator of `S` is the coefficient of `S`, modulo `2^W`.** -/
theorem accOf_coeff {V : ℕ} (F : Formula V) (W D s : ℕ) (hs : s < 2 ^ V) (hD : (setOf V s).card ≤ D) :
    (accOf V W ((famRecs V D).map (valRec V W F)) (s + (setOf V s).card * 2 ^ V) : ℤ) ≡
      coeff F.expand (setOf V s) [ZMOD 2 ^ W] := by
  rw [← sum_termZ F D s hD]
  exact accOf_modEq F W D s _ hs

/-! ## Decoding -/

/-- Two's complement decoding of a `W`-bit accumulator. -/
def decodeAcc (W a : ℕ) : ℤ := if a < 2 ^ (W - 1) then a else (a : ℤ) - 2 ^ W

theorem decodeAcc_eq (W a : ℕ) (c : ℤ) (hW : 1 ≤ W) (ha : a < 2 ^ W) (hc : c.natAbs < 2 ^ (W - 1))
    (hm : (a : ℤ) ≡ c [ZMOD 2 ^ W]) : decodeAcc W a = c := by
  obtain ⟨H, hH⟩ : ∃ H, 2 ^ (W - 1) = H := ⟨_, rfl⟩
  have hHn : 2 ^ W = 2 * H := by rw [← hH, ← pow_succ']; congr 1; omega
  have hHz : (2 : ℤ) ^ W = 2 * (H : ℤ) := by exact_mod_cast hHn
  rw [hH] at hc
  rw [hHn] at ha
  obtain ⟨k, hk⟩ := hm.dvd
  rw [hHz] at hk
  have hc1 : -(H : ℤ) < c ∧ c < H := by
    rcases Int.natAbs_eq c with h | h <;> constructor <;> omega
  have hk0 : k ≤ 0 := by
    by_contra h0
    have : 2 * (H : ℤ) * 1 ≤ 2 * H * k := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  have hk1 : -1 ≤ k := by
    by_contra h0
    have : 2 * (H : ℤ) * k ≤ 2 * H * (-2) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  unfold decodeAcc
  rw [hH, hHz]
  rcases (show k = 0 ∨ k = -1 by omega) with rfl | rfl
  · rw [if_pos (by omega)]; omega
  · rw [if_neg (by omega)]; omega

/-- **The decoded accumulator of `S` is the coefficient of `S`** (for `W ≥ weight + 2`). -/
theorem decode_accOf {V : ℕ} (F : Formula V) (W D s : ℕ) (hs : s < 2 ^ V) (hD : (setOf V s).card ≤ D)
    (hW : F.weight + 2 ≤ W) :
    decodeAcc W (accOf V W ((famRecs V D).map (valRec V W F)) (s + (setOf V s).card * 2 ^ V)) =
      coeff F.expand (setOf V s) := by
  apply decodeAcc_eq W _ _ (by omega) (accOf_lt _ _ _ _) _ (accOf_coeff F W D s hs hD)
  have h1 := expandM_coeff_le F (setOf V s)
  have h2 := Formula.mass_le_two_pow_weight F
  have h3 : 2 ^ F.weight < 2 ^ (W - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem decodeAcc_zero (W a : ℕ) (ha : a < 2 ^ W) : decodeAcc W a = 0 ↔ a = 0 := by
  unfold decodeAcc
  split_ifs with h
  · omega
  · constructor
    · intro e; exfalso; have : (a : ℤ) < 2 ^ W := by exact_mod_cast ha
      omega
    · intro e; subst e; exfalso; exact h (Nat.two_pow_pos _)

end NearCubicGates.Close.Expand

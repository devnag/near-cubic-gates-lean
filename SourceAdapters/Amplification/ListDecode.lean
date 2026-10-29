import SourceAdapters.Amplification.Hadamard

/-!
# A01 step 4: decoding the concatenation with the Hadamard code (STV Lemma 28's analysis)

STV text l.890–905 (proof of Lemma 28): "Given i ∈ [n], we consider the oracle r|_i : [2^t] → {0,1} given by
r|_i(j) = r(i,j). We find a list of all elements z ∈ [q] such that Had(z) has agreement at least 1/2 + ε/2 with
r|_i. By Lemma 27, this list has at most 1/ε² elements. The oracle r'_m, on query i, outputs the m'th element of
this list (after sorting them using some canonical order …). … An application of Markov's inequality yields that
for at least ε/2 fraction of the indices i ∈ [n], r|_i has at least 1/2 + ε/2 agreement with Had(y(i)), and
therefore r|_i = r'_m(i) for some m. Since there are only 1/ε² choices for m, it follows by averaging that there
exists a m0 such that r'_{m0}(i) = y(i) for at least a fraction (ε/2)·ε² = ε³/2 of the indices i ∈ [n]."

Here the blocks are indexed by any finite type `Z` (later `F^m`), the inner symbols are `t`-bit words, the canonical
order is the order of the little-endian codes `0 … 2^t − 1` (`slot`), and the received word `B` has agreement
**more than** `1/2 + δ` (the strict threshold of Theorem 24 as used in `app:sources`, "Full-range amplification interface"). The Markov step gives
more than a `δ` fraction of good blocks (STV's `ε/2` is a weaker bound), hence the slot `j0 < ⌊1/δ²⌋` with
agreement **more than `δ³`** (`exists_good_slot`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset

variable {t : ℕ}

/-- The word of the little-endian code `c`. -/
def wordOfCode (c : ℕ) : Fin t → Bool := fun s => c.testBit s.val

/-- The list of `r`: the words whose Hadamard codeword agrees with `r` on at least `(1/2 + η)·2^t` positions. -/
noncomputable def hadList (η : ℝ) (r : (Fin t → Bool) → Bool) : Finset (Fin t → Bool) :=
  univ.filter fun a => (1 / 2 + η) * 2 ^ t ≤ (agreeCount r a : ℝ)

/-- The listed codes in increasing order. -/
noncomputable def hadCodes (η : ℝ) (r : (Fin t → Bool) → Bool) : List ℕ :=
  (List.range (2 ^ t)).filter fun c => decide (wordOfCode c ∈ hadList η r)

/-- `r'_j`: the `j`-th listed word in the canonical order (the zero word when the list is shorter). -/
noncomputable def slot (η : ℝ) (j : ℕ) (r : (Fin t → Bool) → Bool) : Fin t → Bool :=
  wordOfCode ((hadCodes η r).getD j 0)

theorem wordOfCode_codeOf (a : Fin t → Bool) :
    ∃ c < 2 ^ t, wordOfCode c = a := by
  refine ⟨∑ s : Fin t, (a s).toNat * 2 ^ s.val, ?_, ?_⟩
  · have : ∀ n (b : Fin n → Bool), ∑ s : Fin n, (b s).toNat * 2 ^ s.val < 2 ^ n := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih =>
        intro b
        rw [Fin.sum_univ_castSucc]
        have h1 := ih (fun s => b s.castSucc)
        have h2 : (b (Fin.last n)).toNat ≤ 1 := Bool.toNat_le _
        simp only [Fin.val_last, Fin.val_castSucc] at h1 ⊢
        have h3 := Nat.mul_le_mul_right (2 ^ n) h2
        rw [pow_succ]; omega
    exact this t a
  · funext s
    unfold wordOfCode
    have key : ∀ n (b : Fin n → Bool) (i : Fin n), (∑ s : Fin n, (b s).toNat * 2 ^ s.val).testBit i.val = b i := by
      intro n
      induction n with
      | zero => intro b i; exact i.elim0
      | succ n ih =>
        intro b i
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
        have hsh : ∑ s : Fin n, (b s.succ).toNat * 2 ^ (s.val + 1) = 2 * ∑ s : Fin n, (b s.succ).toNat * 2 ^ s.val := by
          rw [mul_sum]; refine sum_congr rfl fun s _ => ?_; ring
        rw [hsh]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.val_zero]
          cases b 0 <;> simp [Nat.testBit_zero]
        · simp only [Fin.val_succ]
          have := ih (fun s => b s.succ) i
          cases h0 : b 0
          · simp only [Bool.toNat_false, zero_add]
            rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by norm_num)]; exact this
          · simp only [Bool.toNat_true]
            rw [Nat.testBit_succ, show 1 + 2 * ∑ s : Fin n, (b s.succ).toNat * 2 ^ s.val =
              2 * ∑ s : Fin n, (b s.succ).toNat * 2 ^ s.val + 1 by ring, Nat.mul_add_div (by norm_num)]
            simpa using this
    exact key t a s

/-- Every listed word occupies some slot below the list's size. -/
theorem exists_slot (η : ℝ) (r : (Fin t → Bool) → Bool) (a : Fin t → Bool) (ha : a ∈ hadList η r) :
    ∃ j < (hadList η r).card, slot η j r = a := by
  obtain ⟨c, hc, rfl⟩ := wordOfCode_codeOf (t := t) a
  have hmem : c ∈ hadCodes η r := List.mem_filter.mpr ⟨List.mem_range.mpr hc, by simpa using ha⟩
  obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hmem
  have hnodup : (hadCodes η r).Nodup := (List.nodup_range).filter _
  have hlen : (hadCodes η r).length ≤ (hadList η r).card := by
    have hinj : ∀ c ∈ hadCodes η r, ∀ c' ∈ hadCodes η r, wordOfCode (t := t) c = wordOfCode c' → c = c' := by
      intro c1 h1 c2 h2 heq
      have h1' := List.mem_range.mp (List.mem_filter.mp h1).1
      have h2' := List.mem_range.mp (List.mem_filter.mp h2).1
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < t
      · exact congrFun heq ⟨i, hi⟩
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1' (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le h2' (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    have himg : ((hadCodes η r).toFinset.image (wordOfCode (t := t))) ⊆ hadList η r := by
      intro a ha
      obtain ⟨c, hc, rfl⟩ := mem_image.mp ha
      have := (List.mem_filter.mp (List.mem_toFinset.mp hc)).2
      simpa using this
    calc (hadCodes η r).length = (hadCodes η r).toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
      _ = ((hadCodes η r).toFinset.image (wordOfCode (t := t))).card := by
          rw [card_image_of_injOn]
          intro c1 h1 c2 h2 heq
          exact hinj c1 (List.mem_toFinset.mp h1) c2 (List.mem_toFinset.mp h2) heq
      _ ≤ (hadList η r).card := card_le_card himg
  refine ⟨j, lt_of_lt_of_le hj hlen, ?_⟩
  unfold slot
  rw [List.getD_eq_getElem _ _ hj, hjc]

/-- The list of a block has at most `⌊1/δ²⌋` words (Lemma 27 with `η = δ/2`). -/
theorem hadList_card_le (δ : ℝ) (hδ : 0 < δ) (r : (Fin t → Bool) → Bool) :
    (hadList (δ / 2) r).card ≤ ⌊1 / δ ^ 2⌋₊ := by
  apply Nat.le_floor
  have h := hadamard_list_bound r (δ / 2) (by positivity)
  have e : 1 / (4 * (δ / 2) ^ 2) = 1 / δ ^ 2 := by field_simp; ring
  rw [e] at h
  exact h

/-- **Markov's inequality for the blocks**: if the concatenated word agrees with `B` on more than a `1/2 + δ`
fraction, more than a `δ` fraction of the blocks agree with their Hadamard codeword on at least `1/2 + δ/2`. -/
theorem many_good_blocks {Z : Type} [Fintype Z] (Y : Z → Fin t → Bool) (B : Z → (Fin t → Bool) → Bool)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hagree : (1 / 2 + δ) * (Fintype.card Z * 2 ^ t) < ∑ z, (agreeCount (B z) (Y z) : ℝ)) :
    δ * Fintype.card Z < ((univ.filter fun z => Y z ∈ hadList (δ / 2) (B z)).card : ℝ) := by
  set G := univ.filter fun z => Y z ∈ hadList (δ / 2) (B z)
  have hT : (0 : ℝ) < 2 ^ t := by positivity
  have hle : ∀ z, (agreeCount (B z) (Y z) : ℝ) ≤ 2 ^ t := by
    intro z
    have : agreeCount (B z) (Y z) ≤ 2 ^ t := by
      unfold agreeCount
      calc _ ≤ (univ : Finset (Fin t → Bool)).card := card_filter_le _ _
        _ = 2 ^ t := by simp
    exact_mod_cast this
  have hbad : ∀ z ∈ univ.filter (fun z => ¬ (Y z ∈ hadList (δ / 2) (B z))),
      (agreeCount (B z) (Y z) : ℝ) ≤ (1 / 2 + δ / 2) * 2 ^ t := by
    intro z hz
    have h := (mem_filter.mp hz).2
    simp only [hadList, mem_filter, mem_univ, true_and, not_le] at h
    exact h.le
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset Z) (fun z => Y z ∈ hadList (δ / 2) (B z))
    (fun z => (agreeCount (B z) (Y z) : ℝ))
  have hG : ∑ z ∈ G, (agreeCount (B z) (Y z) : ℝ) ≤ G.card * 2 ^ t := by
    calc _ ≤ ∑ _z ∈ G, (2 : ℝ) ^ t := sum_le_sum fun z _ => hle z
      _ = G.card * 2 ^ t := by rw [sum_const, nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset Z)) (fun z => Y z ∈ hadList (δ / 2) (B z))
  rw [card_univ] at hcard
  have hB : ∑ z ∈ univ.filter (fun z => ¬ (Y z ∈ hadList (δ / 2) (B z))), (agreeCount (B z) (Y z) : ℝ) ≤
      ((Fintype.card Z : ℝ) - G.card) * ((1 / 2 + δ / 2) * 2 ^ t) := by
    calc _ ≤ ∑ _z ∈ univ.filter (fun z => ¬ (Y z ∈ hadList (δ / 2) (B z))), (1 / 2 + δ / 2) * (2 : ℝ) ^ t :=
          sum_le_sum hbad
      _ = _ := by
          rw [sum_const, nsmul_eq_mul]
          congr 1
          have : ((univ.filter fun z => ¬ (Y z ∈ hadList (δ / 2) (B z))).card : ℝ) = Fintype.card Z - G.card := by
            rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast hcard
          exact this
  have hsum : ∑ z, (agreeCount (B z) (Y z) : ℝ) ≤
      G.card * 2 ^ t + ((Fintype.card Z : ℝ) - G.card) * ((1 / 2 + δ / 2) * 2 ^ t) := by
    rw [← hsplit]; exact add_le_add hG hB
  have hGle : (G.card : ℝ) ≤ Fintype.card Z := by exact_mod_cast card_le_univ G
  set N : ℝ := (Fintype.card Z : ℝ)
  set g : ℝ := (G.card : ℝ)
  have h3 : (1 / 2 + δ) * N < g + (N - g) * (1 / 2 + δ / 2) := by
    by_contra hc
    push Not at hc
    have h4 := mul_le_mul_of_nonneg_right hc hT.le
    have h5 : (1 / 2 + δ) * (N * 2 ^ t) < g * 2 ^ t + (N - g) * ((1 / 2 + δ / 2) * 2 ^ t) := by linarith
    nlinarith
  by_contra hc
  push Not at hc
  have h6 : g * (1 / 2 - δ / 2) ≤ δ * N * (1 / 2 - δ / 2) := mul_le_mul_of_nonneg_right hc (by linarith)
  have h7 : 0 ≤ δ * N * δ := by positivity
  nlinarith

/-- **The averaging step**: some slot `j0 < ⌊1/δ²⌋` agrees with the inner codeword `Y` on more than a `δ³`
fraction of the blocks. -/
theorem exists_good_slot {Z : Type} [Fintype Z] (Y : Z → Fin t → Bool) (B : Z → (Fin t → Bool) → Bool)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hagree : (1 / 2 + δ) * (Fintype.card Z * 2 ^ t) < ∑ z, (agreeCount (B z) (Y z) : ℝ)) :
    ∃ j < ⌊1 / δ ^ 2⌋₊,
      δ ^ 3 * Fintype.card Z < ((univ.filter fun z => slot (δ / 2) j (B z) = Y z).card : ℝ) := by
  classical
  set J := ⌊1 / δ ^ 2⌋₊
  set G := univ.filter fun z => Y z ∈ hadList (δ / 2) (B z)
  have hG := many_good_blocks Y B δ hδ hδ1 hagree
  have hsub : G ⊆ (range J).biUnion fun j => univ.filter fun z => slot (δ / 2) j (B z) = Y z := by
    intro z hz
    have hz' := (mem_filter.mp hz).2
    obtain ⟨j, hj, hjs⟩ := exists_slot (δ / 2) (B z) (Y z) hz'
    exact mem_biUnion.mpr ⟨j, mem_range.mpr (lt_of_lt_of_le hj (hadList_card_le δ hδ (B z))),
      mem_filter.mpr ⟨mem_univ z, hjs⟩⟩
  have hcount : (G.card : ℝ) ≤ ∑ j ∈ range J, ((univ.filter fun z => slot (δ / 2) j (B z) = Y z).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hJpos : 0 < J := by
    by_contra h
    have h0 : J = 0 := by omega
    rw [h0, range_zero, sum_empty] at hcount
    have : (0 : ℝ) ≤ δ * Fintype.card Z := by positivity
    linarith
  have hJle : (J : ℝ) ≤ 1 / δ ^ 2 := Nat.floor_le (by positivity)
  by_contra hno
  push Not at hno
  have hsum : ∑ j ∈ range J, ((univ.filter fun z => slot (δ / 2) j (B z) = Y z).card : ℝ) ≤
      J * (δ ^ 3 * Fintype.card Z) := by
    calc _ ≤ ∑ _j ∈ range J, δ ^ 3 * (Fintype.card Z : ℝ) := sum_le_sum fun j hj => hno j (mem_range.mp hj)
      _ = J * (δ ^ 3 * Fintype.card Z) := by rw [sum_const, card_range, nsmul_eq_mul]
  have h3 : (J : ℝ) * (δ ^ 3 * Fintype.card Z) ≤ δ * Fintype.card Z := by
    have hZ : (0 : ℝ) ≤ Fintype.card Z := by positivity
    have this : (J : ℝ) * δ ^ 2 ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hJle; linarith
    calc (J : ℝ) * (δ ^ 3 * Fintype.card Z) = (J * δ ^ 2) * (δ * Fintype.card Z) := by ring
      _ ≤ 1 * (δ * Fintype.card Z) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = δ * Fintype.card Z := one_mul _
  linarith

end NearCubicGates.Adapters.Amplification

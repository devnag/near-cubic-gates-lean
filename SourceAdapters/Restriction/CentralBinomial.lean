import NineInputs

/-!
# Field 2 (`restriction`): the central binomial restriction bound, proved

`NearCubicGates.Adapters.Restriction.centralBinomialRestriction :
  NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction`
(`Statement.lean` §27, l.1276–1280; `NineInputs.restriction`). No hypotheses: this field needs no published
leaf.

Paper:
- `lem:live`, Lemma `lem:live`: "For a threshold gate \(g\), a uniform \(k\)-subset \(I\subseteq[n]\), and
  uniform outer assignment \(y\), \Pr[g\text{ is live on }C_y] \le \frac{k\binom{n-k}{\floor{(n-k)/2}}}{2^{n-k}}"
  (the first inequality is this field; the second and the Markov step are proved downstream in
  `Proof/Gates/Counter/SamplingLive.lean`).
- proof of `lem:live` (`app:live`): "A threshold gate is unate, so the chain-counting argument in the proof of
  \cite[Lemma~A.3.1]{CTW26}, which combines their (14) and (15), bounds the fraction of restrictions leaving
  \(g\) live by \(k\binom{n-k}{\floor{(n-k)/2}}2^{-(n-k)}\)."

Source context: Chen–Tal–Wang, Appendix A.3 (`adapters/sourcetext/CTW26.txt`), Lemma A.3.1 and the display after
its (15). CTW26 double counts (restriction, maximal chain) pairs. This proof uses an equivalent exact count
without chains: after flipping the negative-weight coordinates the gate is a monotone `F` on `Finset (Fin n)`;
a restriction `(I, y)` is live only if `F a = false` and `F (a ∪ I) = true`, `a` the set of fixed coordinates
set to the term-raising value. With `zeroCount F s` the number of `F`-zeros of size `s` and
`d s = zeroCount F s / C(n, s)`, the live pairs `(I, a)` with `|a| = p` number exactly
`C(n,k)·C(n−k,p)·(d p − d (p+k))` (the zero set is a down-set), and `∑_{p ≤ n−k} (d p − d (p+k)) ≤ k`
telescopes. Since `C(n−k,p) ≤ C(n−k,⌊(n−k)/2⌋)`, the live count is at most `k·C(n,k)·C(n−k,⌊(n−k)/2⌋)`, and
there are `C(n,k)·2^{n−k}` restrictions. The whole quantified range `0 < k < n` is covered; no `k ≤ √n` reduction is used.

Port of `audit/lean/Audit/Step4/Input2.lean` (`Audit.Step4.input2`), renamed; proofs unchanged.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Restriction

open scoped BigOperators
open Finset

/-! ## 1. Counting core: a monotone Boolean function on subsets of `Fin n` -/

section Core

variable {n : ℕ}

/-- `F` is monotone (an up-set indicator). -/
def IsUpSetIndicator (F : Finset (Fin n) → Bool) : Prop :=
  ∀ A B : Finset (Fin n), A ⊆ B → F A = true → F B = true

/-- Indicator of an `F`-zero. -/
def zeroIndicator (F : Finset (Fin n) → Bool) (a : Finset (Fin n)) : ℝ := if F a = true then 0 else 1

/-- Indicator of a live pair `(I, a)`: bottom `a` is a zero, top `a ∪ I` is a one. -/
def livePairIndicator (F : Finset (Fin n) → Bool) (I a : Finset (Fin n)) : ℝ :=
  if F a = false ∧ F (a ∪ I) = true then 1 else 0

/-- Number of `F`-zeros of size `s`. -/
def zeroCount (F : Finset (Fin n) → Bool) (s : ℕ) : ℝ :=
  ∑ a ∈ powersetCard s (univ : Finset (Fin n)), zeroIndicator F a

/-- Density of `F`-zeros at level `s`. -/
noncomputable def zeroDensity (F : Finset (Fin n) → Bool) (s : ℕ) : ℝ := zeroCount F s / (n.choose s : ℝ)

lemma zeroIndicator_nonneg (F : Finset (Fin n) → Bool) (a : Finset (Fin n)) : 0 ≤ zeroIndicator F a := by
  unfold zeroIndicator; split_ifs <;> norm_num

lemma zeroIndicator_le_one (F : Finset (Fin n) → Bool) (a : Finset (Fin n)) : zeroIndicator F a ≤ 1 := by
  unfold zeroIndicator; split_ifs <;> norm_num

lemma livePairIndicator_nonneg (F : Finset (Fin n) → Bool) (I a : Finset (Fin n)) : 0 ≤ livePairIndicator F I a := by
  unfold livePairIndicator; split_ifs <;> norm_num

lemma livePairIndicator_eq {F : Finset (Fin n) → Bool} (hF : IsUpSetIndicator F) (I a : Finset (Fin n)) :
    livePairIndicator F I a = zeroIndicator F a - zeroIndicator F (a ∪ I) := by
  have hmono := hF a (a ∪ I) subset_union_left
  unfold livePairIndicator zeroIndicator
  cases h1 : F a <;> cases h2 : F (a ∪ I) <;> simp_all

lemma zeroDensity_nonneg (F : Finset (Fin n) → Bool) (s : ℕ) : 0 ≤ zeroDensity F s := by
  unfold zeroDensity zeroCount
  exact div_nonneg (sum_nonneg fun a _ => zeroIndicator_nonneg F a) (Nat.cast_nonneg _)

lemma zeroDensity_le_one (F : Finset (Fin n) → Bool) (s : ℕ) : zeroDensity F s ≤ 1 := by
  unfold zeroDensity
  have hZ : zeroCount F s ≤ (n.choose s : ℝ) := by
    unfold zeroCount
    calc ∑ a ∈ powersetCard s (univ : Finset (Fin n)), zeroIndicator F a
        ≤ ∑ a ∈ powersetCard s (univ : Finset (Fin n)), (1 : ℝ) := sum_le_sum fun a _ => zeroIndicator_le_one F a
      _ = (n.choose s : ℝ) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rcases Nat.eq_zero_or_pos (n.choose s) with h | h
  · rw [h, Nat.cast_zero, div_zero]; norm_num
  · rw [div_le_one (by exact_mod_cast h)]; exact hZ

/-- First half of the level identity: pairs whose bottom is a zero. -/
lemma sum_zero_bottoms (F : Finset (Fin n) → Bool) (k p : ℕ) :
    ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, zeroIndicator F a =
      zeroCount F p * ((n - p).choose k : ℝ) := by
  rw [Finset.sum_comm' (t' := powersetCard p (univ : Finset (Fin n)))
    (s' := fun a => powersetCard k aᶜ)]
  · unfold zeroCount
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hca : a.card = p := (mem_powersetCard.1 ha).2
    rw [sum_const, card_powersetCard, card_compl, Fintype.card_fin, hca, nsmul_eq_mul, mul_comm]
  · intro I a
    simp only [mem_powersetCard, subset_univ, true_and, subset_compl_iff_disjoint_right]
    rw [disjoint_comm]
    tauto

/-- Second half of the level identity: pairs whose top is a zero (then the bottom is one too). -/
lemma sum_zero_tops (F : Finset (Fin n) → Bool) (k p : ℕ) :
    ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, zeroIndicator F (a ∪ I) =
      zeroCount F (p + k) * ((p + k).choose k : ℝ) := by
  have inner : ∀ I ∈ powersetCard k (univ : Finset (Fin n)),
      ∑ a ∈ powersetCard p Iᶜ, zeroIndicator F (a ∪ I) =
        ∑ b ∈ (powersetCard (p + k) (univ : Finset (Fin n))).filter (fun b => I ⊆ b), zeroIndicator F b := by
    intro I hI
    have hcI : I.card = k := (mem_powersetCard.1 hI).2
    apply Finset.sum_nbij' (fun a => a ∪ I) (fun b => b \ I)
    · intro a ha
      have ha' := mem_powersetCard.1 ha
      have hdis : Disjoint a I := subset_compl_iff_disjoint_right.1 ha'.1
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      exact ⟨by rw [card_union_of_disjoint hdis, ha'.2, hcI], subset_union_right⟩
    · intro b hb
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hb
      simp only [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [mem_sdiff] at hx
        exact mem_compl.2 hx.2
      · rw [card_sdiff_of_subset hb.2, hb.1, hcI]; omega
    · intro a ha
      have hdis : Disjoint a I := subset_compl_iff_disjoint_right.1 (mem_powersetCard.1 ha).1
      exact union_sdiff_cancel_right hdis
    · intro b hb
      simp only [mem_filter] at hb
      exact sdiff_union_of_subset hb.2
    · intro a _
      rfl
  rw [Finset.sum_congr rfl inner]
  rw [Finset.sum_comm' (t' := powersetCard (p + k) (univ : Finset (Fin n)))
    (s' := fun b => powersetCard k b)]
  · unfold zeroCount
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hcb : b.card = p + k := (mem_powersetCard.1 hb).2
    rw [sum_const, card_powersetCard, hcb, nsmul_eq_mul, mul_comm]
  · intro I b
    simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
    tauto

/-- `C(n,p)·C(n−p,k) = C(n,k)·C(n−k,p)` and `C(n,p+k)·C(p+k,k) = C(n,k)·C(n−k,p)`. -/
lemma choose_mul_choose_top (k p : ℕ) :
    n.choose (p + k) * (p + k).choose k = n.choose k * (n - k).choose p := by
  rw [Nat.choose_mul (Nat.le_add_left k p), Nat.add_sub_cancel]

lemma choose_mul_choose_bottom (k p : ℕ) :
    n.choose p * (n - p).choose k = n.choose k * (n - k).choose p := by
  have h := Nat.choose_mul (n := n) (k := p + k) (s := p) (Nat.le_add_right p k)
  rw [Nat.add_sub_cancel_left] at h
  rw [← h, Nat.choose_symm_add, choose_mul_choose_top]

/-- The level identity: live pairs with `|a| = p`. -/
lemma livePairs_level_eq {F : Finset (Fin n) → Bool} (hF : IsUpSetIndicator F) (k p : ℕ) (hpk : p + k ≤ n) :
    ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, livePairIndicator F I a =
      (n.choose k : ℝ) * ((n - k).choose p : ℝ) * (zeroDensity F p - zeroDensity F (p + k)) := by
  have hsplit : ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, livePairIndicator F I a =
      (∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, zeroIndicator F a) -
        ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, zeroIndicator F (a ∪ I) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun I _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun a _ => livePairIndicator_eq hF I a
  rw [hsplit, sum_zero_bottoms, sum_zero_tops]
  unfold zeroDensity
  have h1 : ((n.choose (p + k) : ℕ) : ℝ) * ((p + k).choose k : ℕ) =
      (n.choose k : ℝ) * ((n - k).choose p : ℝ) := by exact_mod_cast choose_mul_choose_top k p
  have h2 : ((n.choose p : ℕ) : ℝ) * ((n - p).choose k : ℕ) =
      (n.choose k : ℝ) * ((n - k).choose p : ℝ) := by exact_mod_cast choose_mul_choose_bottom k p
  have hp0 : (n.choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hpk0 : (n.choose (p + k) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hpk).ne'
  have e1 : (n.choose k : ℝ) * ((n - k).choose p : ℝ) * (zeroCount F p / (n.choose p : ℝ)) =
      zeroCount F p * ((n - p).choose k : ℝ) := by
    rw [← h2]; field_simp
  have e2 : (n.choose k : ℝ) * ((n - k).choose p : ℝ) * (zeroCount F (p + k) / (n.choose (p + k) : ℝ)) =
      zeroCount F (p + k) * ((p + k).choose k : ℝ) := by
    rw [← h1]; field_simp
  rw [mul_sub, e1, e2]

/-- Telescoping with step `k`. -/
lemma sum_range_sub_shift_le (d : ℕ → ℝ) (h0 : ∀ s, 0 ≤ d s) (h1 : ∀ s, d s ≤ 1) (k M : ℕ) :
    ∑ p ∈ range M, (d p - d (p + k)) ≤ k := by
  have e1 := Finset.sum_range_add d M k
  have e2 := Finset.sum_range_add d k M
  rw [Finset.sum_sub_distrib]
  have hre : ∑ p ∈ range M, d (p + k) = ∑ x ∈ range M, d (k + x) :=
    sum_congr rfl fun x _ => by rw [add_comm]
  rw [hre]
  have hsum : ∑ x ∈ range k, d x ≤ k := by
    calc ∑ x ∈ range k, d x ≤ ∑ _x ∈ range k, (1 : ℝ) := sum_le_sum fun x _ => h1 x
      _ = k := by simp
  have hnn : 0 ≤ ∑ x ∈ range k, d (M + x) := sum_nonneg fun x _ => h0 _
  rw [add_comm M k] at e1
  linarith

/-- The counting core: live pairs `(I, a)`, `|I| = k`, `a ⊆ Iᶜ`, number at most `k·C(n,k)·C(n−k,⌊(n−k)/2⌋)`. -/
theorem livePairs_le {F : Finset (Fin n) → Bool} (hF : IsUpSetIndicator F) (k : ℕ) (hk : k ≤ n) :
    ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ Iᶜ.powerset, livePairIndicator F I a ≤
      (k : ℝ) * (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) := by
  have hsplit : ∀ I ∈ powersetCard k (univ : Finset (Fin n)),
      ∑ a ∈ Iᶜ.powerset, livePairIndicator F I a =
        ∑ p ∈ range (n - k + 1), ∑ a ∈ powersetCard p Iᶜ, livePairIndicator F I a := by
    intro I hI
    have hc : Iᶜ.card = n - k := by
      rw [card_compl, Fintype.card_fin, (mem_powersetCard.1 hI).2]
    rw [powerset_card_disjiUnion, sum_disjiUnion, hc]
  rw [sum_congr rfl hsplit, sum_comm]
  have hlev : ∀ p ∈ range (n - k + 1),
      ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, livePairIndicator F I a ≤
        (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) * (zeroDensity F p - zeroDensity F (p + k)) := by
    intro p hp
    have hpk : p + k ≤ n := by rw [mem_range] at hp; omega
    have hL : 0 ≤ ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, livePairIndicator F I a :=
      sum_nonneg fun I _ => sum_nonneg fun a _ => livePairIndicator_nonneg F I a
    rw [livePairs_level_eq hF k p hpk] at hL ⊢
    have hpos : 0 < (n.choose k : ℝ) * ((n - k).choose p : ℝ) := by
      have a1 : 0 < n.choose k := Nat.choose_pos hk
      have a2 : 0 < (n - k).choose p := Nat.choose_pos (by omega)
      positivity
    have hd : 0 ≤ zeroDensity F p - zeroDensity F (p + k) := (mul_nonneg_iff_of_pos_left hpos).1 hL
    have hc : ((n - k).choose p : ℝ) ≤ ((n - k).choose ((n - k) / 2) : ℝ) := by
      exact_mod_cast Nat.choose_le_middle p (n - k)
    have hnk : (0 : ℝ) ≤ n.choose k := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hnk) hd
  calc ∑ p ∈ range (n - k + 1),
        ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ powersetCard p Iᶜ, livePairIndicator F I a
      ≤ ∑ p ∈ range (n - k + 1),
          (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) * (zeroDensity F p - zeroDensity F (p + k)) :=
        sum_le_sum hlev
    _ = (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) *
          ∑ p ∈ range (n - k + 1), (zeroDensity F p - zeroDensity F (p + k)) := by rw [mul_sum]
    _ ≤ (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) * k := by
        apply mul_le_mul_of_nonneg_left
        · exact sum_range_sub_shift_le (zeroDensity F) (zeroDensity_nonneg F) (zeroDensity_le_one F) k _
        · positivity
    _ = (k : ℝ) * (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) := by ring

end Core

/-! ## 2. The gate as a monotone function after flipping the negative-weight coordinates -/

section Gate

open NearCubicWires NearCubicGates NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness

variable {n : ℕ}

/-- Flip mask: the coordinates with negative weight (CTW26 p. 27: "we can flip some input bits to make `f`
monotone"). -/
noncomputable def negativeWeight (g : RealThresholdGate n) (i : Fin n) : Bool := decide (g.weight i < 0)

/-- The input whose term-raising coordinates are exactly `A`. -/
noncomputable def raisedPoint (g : RealThresholdGate n) (A : Finset (Fin n)) : BitInput n :=
  fun i => xor (decide (i ∈ A)) (negativeWeight g i)

lemma xor_decide_ne (b c : Bool) : xor (decide (b ≠ c)) c = b := by
  cases b <;> cases c <;> rfl

/-- The gate read on subsets: monotone. -/
noncomputable def gateOnRaisedSets (g : RealThresholdGate n) (A : Finset (Fin n)) : Bool := g.eval (raisedPoint g A)

lemma gateOnRaisedSets_mono (g : RealThresholdGate n) : IsUpSetIndicator (gateOnRaisedSets g) := by
  intro A B hAB hA
  unfold gateOnRaisedSets RealThresholdGate.eval at *
  rw [decide_eq_true_eq] at hA ⊢
  refine le_trans hA (Finset.sum_le_sum fun i _ => ?_)
  unfold raisedPoint negativeWeight
  by_cases hiA : i ∈ A
  · simp [hiA, hAB hiA]
  · by_cases hiB : i ∈ B
    · by_cases hw : g.weight i < 0
      · simp [hiA, hiB, hw, bitAsReal]; linarith
      · simp [hiA, hiB, hw, bitAsReal]; linarith
    · simp [hiA, hiB]

/-- The fixed coordinates that the outer assignment sets to the term-raising value. -/
noncomputable def cellBottom (g : RealThresholdGate n) {k : ℕ} (ρ : FiniteRestriction n k) : Finset (Fin n) :=
  univ.filter (fun j => ∃ h : j ∉ ρ.1.val, ρ.2 ⟨j, h⟩ ≠ negativeWeight g j)

lemma mem_cellBottom (g : RealThresholdGate n) {k : ℕ} (ρ : FiniteRestriction n k) (j : Fin n) :
    j ∈ cellBottom g ρ ↔ ∃ h : j ∉ ρ.1.val, ρ.2 ⟨j, h⟩ ≠ negativeWeight g j := by
  unfold cellBottom; simp only [mem_filter, mem_univ, true_and]

lemma cellBottom_subset (g : RealThresholdGate n) {k : ℕ} (ρ : FiniteRestriction n k) :
    cellBottom g ρ ⊆ ρ.1.valᶜ := by
  intro j hj
  rw [mem_cellBottom] at hj
  obtain ⟨h, _⟩ := hj
  exact mem_compl.2 h

/-- Every point of the cell is sandwiched between the cell's bottom `cellBottom` and top `cellBottom ∪ I`. -/
lemma cell_sandwich (g : RealThresholdGate n) {k : ℕ} (ρ : FiniteRestriction n k) (x : BitInput n)
    (hx : cellAgrees ρ x) :
    (gateOnRaisedSets g (cellBottom g ρ) = true → g.eval x = true) ∧
      (g.eval x = true → gateOnRaisedSets g (cellBottom g ρ ∪ ρ.1.val) = true) := by
  obtain ⟨Ax, hmem⟩ : ∃ Ax : Finset (Fin n), ∀ i, i ∈ Ax ↔ x i ≠ negativeWeight g i :=
    ⟨univ.filter (fun i => x i ≠ negativeWeight g i), fun i => by simp⟩
  have hpt : raisedPoint g Ax = x := by
    funext i
    unfold raisedPoint
    rw [decide_eq_decide.2 (hmem i)]
    exact xor_decide_ne (x i) (negativeWeight g i)
  have h1 : cellBottom g ρ ⊆ Ax := by
    intro j hj
    rw [mem_cellBottom] at hj
    obtain ⟨h, hne⟩ := hj
    rw [hmem, hx j h]
    exact hne
  have h2 : Ax ⊆ cellBottom g ρ ∪ ρ.1.val := by
    intro i hi
    rw [hmem] at hi
    rw [mem_union]
    by_cases hI : i ∈ ρ.1.val
    · exact Or.inr hI
    · left
      rw [mem_cellBottom]
      exact ⟨hI, by rw [← hx i hI]; exact hi⟩
  have hev : g.eval x = gateOnRaisedSets g Ax := by unfold gateOnRaisedSets; rw [hpt]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hev]; exact gateOnRaisedSets_mono g _ _ h1 h
  · rw [hev] at h; exact gateOnRaisedSets_mono g _ _ h2 h

/-- A live restriction gives a live pair (bottom zero, top one). -/
lemma indicator_gateLive_le (g : RealThresholdGate n) {k : ℕ} (ρ : FiniteRestriction n k) :
    indicator (gateLive g ρ) ≤ livePairIndicator (gateOnRaisedSets g) ρ.1.val (cellBottom g ρ) := by
  by_cases hl : gateLive g ρ
  · obtain ⟨x, z, hx, hz, hne⟩ := hl
    have sx := cell_sandwich g ρ x hx
    have sz := cell_sandwich g ρ z hz
    have hbot : gateOnRaisedSets g (cellBottom g ρ) = false := by
      cases hb : gateOnRaisedSets g (cellBottom g ρ)
      · rfl
      · exact absurd ((sx.1 hb).trans (sz.1 hb).symm) hne
    have htop : gateOnRaisedSets g (cellBottom g ρ ∪ ρ.1.val) = true := by
      cases ht : gateOnRaisedSets g (cellBottom g ρ ∪ ρ.1.val)
      · exfalso
        apply hne
        have ex : g.eval x = false := by
          cases hxe : g.eval x
          · rfl
          · rw [sx.2 hxe] at ht; exact absurd ht (by simp)
        have ez : g.eval z = false := by
          cases hze : g.eval z
          · rfl
          · rw [sz.2 hze] at ht; exact absurd ht (by simp)
        rw [ex, ez]
      · rfl
    have hlv : gateLive g ρ := ⟨x, z, hx, hz, hne⟩
    unfold indicator livePairIndicator
    simp [hbot, htop, hlv]
  · unfold indicator
    simp only [hl, if_false]
    exact livePairIndicator_nonneg _ _ _

/-- For a fixed `I`, the outer assignments correspond bijectively to the subsets of `Iᶜ`. -/
lemma sum_outerAssignments (g : RealThresholdGate n) {k : ℕ} (I : {I : Finset (Fin n) // I.card = k}) :
    ∑ y : {i : Fin n // i ∉ I.val} → Bool, livePairIndicator (gateOnRaisedSets g) I.val (cellBottom g ⟨I, y⟩) =
      ∑ a ∈ I.valᶜ.powerset, livePairIndicator (gateOnRaisedSets g) I.val a := by
  apply Finset.sum_nbij' (fun y => cellBottom g ⟨I, y⟩)
    (fun a => fun j => xor (decide (j.1 ∈ a)) (negativeWeight g j.1))
  · intro y _
    rw [mem_powerset]
    exact cellBottom_subset g ⟨I, y⟩
  · intro a _
    exact mem_univ _
  · intro y _
    funext j
    have key : (j.1 ∈ cellBottom g ⟨I, y⟩) ↔ y j ≠ negativeWeight g j.1 := by
      rw [mem_cellBottom]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨j.2, h⟩⟩
    rw [decide_eq_decide.2 key]
    exact xor_decide_ne (y j) (negativeWeight g j.1)
  · intro a ha
    rw [mem_powerset] at ha
    ext j
    rw [mem_cellBottom]
    constructor
    · rintro ⟨_, hne⟩
      by_contra hja
      simp [hja] at hne
    · intro hja
      refine ⟨mem_compl.1 (ha hja), ?_⟩
      simp [hja]
  · intro y _
    rfl

lemma card_finiteRestriction (n k : ℕ) : Fintype.card (FiniteRestriction n k) = n.choose k * 2 ^ (n - k) := by
  unfold FiniteRestriction
  rw [Fintype.card_sigma]
  have hc : ∀ I : {I : Finset (Fin n) // I.card = k},
      Fintype.card ({i : Fin n // i ∉ I.val} → Bool) = 2 ^ (n - k) := by
    intro I
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_coe]
    rw [I.property]
  simp only [hc, sum_const, card_univ, Fintype.card_finset_len, Fintype.card_fin, smul_eq_mul]

end Gate

/-! ## 3. Field 2 -/

open NearCubicWires NearCubicGates NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness in
/-- **Field 2 (`NineInputs.restriction`)**, (first inequality of `lem:live`) and proof of `lem:live`:
the fraction of `k`-star restrictions leaving a real threshold gate live is at most
`k·C(n−k,⌊(n−k)/2⌋)/2^{n−k}`, for every `0 < k < n`. No source hypothesis. -/
theorem centralBinomialRestriction :
    NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction := by
  unfold NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction
  intro n k _hk hkn g
  have hkn' : k ≤ n := hkn.le
  have hnum : ∑ ρ : FiniteRestriction n k, indicator (gateLive g ρ) ≤
      (k : ℝ) * (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) := by
    calc ∑ ρ : FiniteRestriction n k, indicator (gateLive g ρ)
        ≤ ∑ ρ : FiniteRestriction n k, livePairIndicator (gateOnRaisedSets g) ρ.1.val (cellBottom g ρ) :=
          sum_le_sum fun ρ _ => indicator_gateLive_le g ρ
      _ = ∑ I : {I : Finset (Fin n) // I.card = k}, ∑ y : {i : Fin n // i ∉ I.val} → Bool,
            livePairIndicator (gateOnRaisedSets g) I.val (cellBottom g ⟨I, y⟩) := Fintype.sum_sigma _
      _ = ∑ I : {I : Finset (Fin n) // I.card = k}, ∑ a ∈ I.valᶜ.powerset, livePairIndicator (gateOnRaisedSets g) I.val a :=
          sum_congr rfl fun I _ => sum_outerAssignments g I
      _ = ∑ I ∈ powersetCard k (univ : Finset (Fin n)), ∑ a ∈ Iᶜ.powerset, livePairIndicator (gateOnRaisedSets g) I a :=
          (Finset.sum_subtype _ (fun I => by simp [mem_powersetCard])
            (fun I => ∑ a ∈ Iᶜ.powerset, livePairIndicator (gateOnRaisedSets g) I a)).symm
      _ ≤ _ := livePairs_le (gateOnRaisedSets_mono g) k hkn'
  unfold mean
  rw [card_finiteRestriction n k]
  have hc : 0 < n.choose k := Nat.choose_pos hkn'
  have hpos : (0 : ℝ) < ((n.choose k * 2 ^ (n - k) : ℕ) : ℝ) := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n - k) := by positivity
  rw [div_le_div_iff₀ hpos h2]
  push_cast
  calc (∑ ρ : FiniteRestriction n k, indicator (gateLive g ρ)) * (2 : ℝ) ^ (n - k)
      ≤ ((k : ℝ) * (n.choose k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ)) * (2 : ℝ) ^ (n - k) :=
        mul_le_mul_of_nonneg_right hnum h2.le
    _ = (k : ℝ) * ((n - k).choose ((n - k) / 2) : ℝ) * ((n.choose k : ℝ) * (2 : ℝ) ^ (n - k)) := by ring

end NearCubicGates.Adapters.Restriction

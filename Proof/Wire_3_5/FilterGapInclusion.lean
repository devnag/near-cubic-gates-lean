import Proof.Wire_3_5.Shared.GapFilter
import Proof.Supplier.SupplierToeplitz

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierPipeline Finset

namespace GapParams
variable (P : GapParams)

theorem prefixBits_le_labelBits : P.prefixBits ≤ P.labelBits := le_max_left _ _

theorem len_le_two_pow_labelBits : P.len ≤ 2 ^ P.labelBits :=
  (Nat.le_pow_clog (by norm_num) P.len).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- `32U ≤ 2^a`: `p ≤ 1/(32U)`. -/
theorem thirtyTwo_cap_le : 32 * P.cap ≤ 2 ^ P.prefixBits := Nat.le_pow_clog (by norm_num) _

/-- `2^a < 64U` for `U ≥ 1`: `p > 1/(64U)`. -/
theorem two_pow_prefixBits_lt (hU : 1 ≤ P.cap) : 2 ^ P.prefixBits < 64 * P.cap := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := 32 * P.cap) (by omega)
  have hpos : 0 < Nat.clog 2 (32 * P.cap) := Nat.clog_pos (by norm_num) (by omega)
  have heq : 2 ^ Nat.clog 2 (32 * P.cap) = 2 ^ (Nat.clog 2 (32 * P.cap)).pred * 2 := by
    rw [← pow_succ, Nat.pred_eq_sub_one]; congr 1; omega
  show 2 ^ Nat.clog 2 (32 * P.cap) < 64 * P.cap
  omega

end GapParams

/-- Distinct coordinates below `2^r` have distinct labels. -/
theorem coordLabel_injective {r i j : ℕ} (hi : i < 2 ^ r) (hj : j < 2 ^ r)
    (h : coordLabel r i = coordLabel r j) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < r
  · have hc := congrFun h ⟨k, hk⟩
    simp only [coordLabel] at hc
    cases hik : i.testBit k <;> cases hjk : j.testBit k <;> simp_all
  · have h2 : 2 ^ r ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem selected_iff (P : GapParams) (h : ToeplitzSeed P.labelBits) (i : ℕ) :
    selected P h i = true ↔ toeplitzHash (coordLabel P.labelBits i) h ∈ zeroPrefixCell P.labelBits P.prefixBits := by
  simp [selected, mem_zeroPrefixCell]

theorem bitAsReal_selected (P : GapParams) (h : ToeplitzSeed P.labelBits) (i : ℕ) :
    bitAsReal (selected P h i) =
      bitAsReal (decide (toeplitzHash (coordLabel P.labelBits i) h ∈ zeroPrefixCell P.labelBits P.prefixBits)) := by
  congr 1
  exact Bool.eq_iff_iff.mpr ((selected_iff P h i).trans (by simp))

theorem sum_bitAsReal_mem (r a : ℕ) :
    (∑ o : SupplierToeplitzCore.BitVec r, bitAsReal (decide (o ∈ zeroPrefixCell r a))) =
      ((zeroPrefixCell r a).card : ℝ) := by
  simp [bitAsReal, Finset.sum_boole]
  rfl

theorem sum_selected (P : GapParams) (i : ℕ) :
    (∑ h : ToeplitzSeed P.labelBits, bitAsReal (selected P h i)) =
      (Fintype.card (ToeplitzSeed P.labelBits) : ℝ) * (1 / 2 ^ P.prefixBits) := by
  simp only [bitAsReal_selected]
  rw [sum_toeplitzHash_exact (coordLabel P.labelBits i)
    (fun o => bitAsReal (decide (o ∈ zeroPrefixCell P.labelBits P.prefixBits))),
    sum_bitAsReal_mem, zeroPrefixCell_card P.prefixBits_le_labelBits, card_toeplitzSeed]
  have ha := P.prefixBits_le_labelBits
  have hsplit : 2 ^ (2 * P.labelBits + (P.labelBits - 1)) =
      2 ^ (P.labelBits + (P.labelBits - 1)) * 2 ^ (P.labelBits - P.prefixBits) * 2 ^ P.prefixBits := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  field_simp

theorem sum_selected_mul (P : GapParams) {i j : ℕ} (hi : i < 2 ^ P.labelBits) (hj : j < 2 ^ P.labelBits)
    (hij : i ≠ j) :
    (∑ h : ToeplitzSeed P.labelBits, bitAsReal (selected P h i) * bitAsReal (selected P h j)) =
      (Fintype.card (ToeplitzSeed P.labelBits) : ℝ) * (1 / 2 ^ P.prefixBits) ^ 2 := by
  simp only [bitAsReal_selected]
  have hne : coordLabel P.labelBits i ≠ coordLabel P.labelBits j := fun h =>
    hij (coordLabel_injective hi hj h)
  rw [sum_toeplitzHash_pair_exact _ _ hne
    (fun o₁ o₂ => bitAsReal (decide (o₁ ∈ zeroPrefixCell P.labelBits P.prefixBits)) *
      bitAsReal (decide (o₂ ∈ zeroPrefixCell P.labelBits P.prefixBits)))]
  rw [← Finset.sum_mul_sum, sum_bitAsReal_mem, zeroPrefixCell_card P.prefixBits_le_labelBits,
    card_toeplitzSeed]
  have ha := P.prefixBits_le_labelBits
  have hsplit : 2 ^ (2 * P.labelBits + (P.labelBits - 1)) =
      2 ^ (P.labelBits - 1) * (2 ^ (P.labelBits - P.prefixBits) * 2 ^ (P.labelBits - P.prefixBits)) *
        (2 ^ P.prefixBits) ^ 2 := by
    rw [← pow_add, ← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  field_simp

/-! ## The selected active count `X` -/

/-- The active coordinates of `Z` (`Z_i = 1`). -/
def activeSet (Z : List Bool) : Finset ℕ := (Finset.range Z.length).filter fun i => Z.getD i false = true

/-- `|active| = w(Z)`. -/
theorem card_activeSet (Z : List Bool) : (activeSet Z).card = Z.count true := by
  induction Z with
  | nil => rfl
  | cons b Z ih =>
    unfold activeSet at ih ⊢
    rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ', ← Finset.card_filter] at *
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.count_cons] at *
    rw [ih]
    cases b <;> simp

theorem mem_activeSet_lt {Z : List Bool} {i : ℕ} (h : i ∈ activeSet Z) : i < Z.length := by
  simp only [activeSet, Finset.mem_filter, Finset.mem_range] at h; exact h.1

theorem selectedActive_eq (P : GapParams) (h : ToeplitzSeed P.labelBits) (Z : List Bool) :
    selectedActive P h Z = (activeSet Z).filter fun i => selected P h i = true := by
  ext i; simp [selectedActive, activeSet, and_assoc]

/-- `X(h) = Σ_{i active} H_i(h)`. -/
theorem card_selectedActive (P : GapParams) (h : ToeplitzSeed P.labelBits) (Z : List Bool) :
    ((selectedActive P h Z).card : ℝ) = ∑ i ∈ activeSet Z, bitAsReal (selected P h i) := by
  rw [selectedActive_eq, Finset.card_filter]
  push_cast
  simp [bitAsReal]

theorem sum_card_selectedActive (P : GapParams) (Z : List Bool) :
    (∑ h : ToeplitzSeed P.labelBits, ((selectedActive P h Z).card : ℝ)) =
      (Fintype.card (ToeplitzSeed P.labelBits) : ℝ) * ((1 / 2 ^ P.prefixBits) * Z.count true) := by
  simp only [card_selectedActive]
  rw [Finset.sum_comm]
  simp only [sum_selected, Finset.sum_const, card_activeSet, nsmul_eq_mul]
  ring

theorem sum_card_selectedActive_sq (P : GapParams) (Z : List Bool) (hZ : Z.length ≤ 2 ^ P.labelBits) :
    (∑ h : ToeplitzSeed P.labelBits, ((selectedActive P h Z).card : ℝ) ^ 2) ≤
      (Fintype.card (ToeplitzSeed P.labelBits) : ℝ) *
        ((1 / 2 ^ P.prefixBits) * Z.count true + ((1 / 2 ^ P.prefixBits) * Z.count true) ^ 2) := by
  set p : ℝ := 1 / 2 ^ P.prefixBits with hp
  set N : ℝ := (Fintype.card (ToeplitzSeed P.labelBits) : ℝ)
  have hp0 : 0 ≤ p := by positivity
  simp only [card_selectedActive, sq, Finset.sum_mul_sum]
  have hterm : ∀ i ∈ activeSet Z, ∀ j ∈ activeSet Z,
      (∑ h : ToeplitzSeed P.labelBits, bitAsReal (selected P h i) * bitAsReal (selected P h j)) =
        if i = j then N * p else N * p ^ 2 := by
    intro i hi j hj
    split_ifs with hij
    · subst hij
      have : ∀ h : ToeplitzSeed P.labelBits,
          bitAsReal (selected P h i) * bitAsReal (selected P h i) = bitAsReal (selected P h i) := by
        intro h; cases selected P h i <;> simp [bitAsReal]
      simp only [this]; exact sum_selected P i
    · exact sum_selected_mul P (by have := mem_activeSet_lt hi; omega)
        (by have := mem_activeSet_lt hj; omega) hij
  have hswap : (∑ h : ToeplitzSeed P.labelBits, ∑ i ∈ activeSet Z, ∑ j ∈ activeSet Z,
      bitAsReal (selected P h i) * bitAsReal (selected P h j)) =
      ∑ i ∈ activeSet Z, ∑ j ∈ activeSet Z,
        ∑ h : ToeplitzSeed P.labelBits, bitAsReal (selected P h i) * bitAsReal (selected P h j) := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hswap]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hterm i hi j hj]
  have hinner : ∀ i ∈ activeSet Z, (∑ j ∈ activeSet Z, if i = j then N * p else N * p ^ 2) ≤
      N * p + (activeSet Z).card * (N * p ^ 2) := by
    intro i hi
    rw [← Finset.add_sum_erase _ _ hi]
    simp only [if_true]
    have hrest : (∑ j ∈ (activeSet Z).erase i, if i = j then N * p else N * p ^ 2) =
        ((activeSet Z).erase i).card * (N * p ^ 2) := by
      rw [Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj).symm]
      simp
    rw [hrest]
    have hc : (((activeSet Z).erase i).card : ℝ) ≤ (activeSet Z).card := by
      exact_mod_cast Finset.card_erase_le
    have : 0 ≤ N * p ^ 2 := by positivity
    nlinarith
  calc (∑ i ∈ activeSet Z, ∑ j ∈ activeSet Z, if i = j then N * p else N * p ^ 2)
      ≤ ∑ _i ∈ activeSet Z, (N * p + (activeSet Z).card * (N * p ^ 2)) := Finset.sum_le_sum hinner
    _ = N * (p * Z.count true + p * Z.count true * (p * Z.count true)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_activeSet]; ring

/-- The union bound: `Pr_h[X>0] ≤ μ`. -/
theorem nonempty_prob_le (P : GapParams) (Z : List Bool) :
    booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) ≤
      (1 / 2 ^ P.prefixBits) * Z.count true := by
  unfold booleanMean
  have hN : (0 : ℝ) < Fintype.card (ToeplitzSeed P.labelBits) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hN]
  calc (∑ h : ToeplitzSeed P.labelBits, bitAsReal (decide (selectedActive P h Z).Nonempty))
      ≤ ∑ h : ToeplitzSeed P.labelBits, ((selectedActive P h Z).card : ℝ) := by
        apply Finset.sum_le_sum; intro h _
        by_cases hne : (selectedActive P h Z).Nonempty
        · simp only [hne, decide_true, bitAsReal, if_true]
          exact_mod_cast hne.card_pos
        · simp [hne, bitAsReal]
    _ = _ := by rw [sum_card_selectedActive]; ring

theorem nonempty_prob_ge (P : GapParams) (Z : List Bool) (hZ : Z.length ≤ 2 ^ P.labelBits) :
    ((1 / 2 ^ P.prefixBits) * Z.count true) / (1 + (1 / 2 ^ P.prefixBits) * Z.count true) ≤
      booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) := by
  set μ : ℝ := (1 / 2 ^ P.prefixBits) * Z.count true with hμ
  set N : ℝ := (Fintype.card (ToeplitzSeed P.labelBits) : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hμ0 : 0 ≤ μ := by positivity
  set X : ToeplitzSeed P.labelBits → ℝ := fun h => ((selectedActive P h Z).card : ℝ)
  set I : ToeplitzSeed P.labelBits → ℝ := fun h => bitAsReal (decide (selectedActive P h Z).Nonempty)
  have hXI : ∀ h, X h * I h = X h := by
    intro h
    by_cases hne : (selectedActive P h Z).Nonempty
    · simp [X, I, hne, bitAsReal]
    · simp [X, I, bitAsReal, Finset.not_nonempty_iff_eq_empty.mp hne]
  have hI2 : ∀ h, I h ^ 2 = I h := by
    intro h; simp only [I]; by_cases hne : (selectedActive P h Z).Nonempty <;> simp [hne, bitAsReal]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ X I
  simp only [hXI, hI2] at hcs
  have hsum : (∑ h, X h) = N * μ := sum_card_selectedActive P Z
  have hsq : (∑ h, X h ^ 2) ≤ N * (μ + μ ^ 2) := sum_card_selectedActive_sq P Z hZ
  have hIsum : 0 ≤ ∑ h, I h := Finset.sum_nonneg fun h _ => by
    simp only [I]; by_cases hne : (selectedActive P h Z).Nonempty <;> simp [hne, bitAsReal]
  unfold booleanMean
  change μ / (1 + μ) ≤ (∑ h, I h) / N
  rw [hsum] at hcs
  rw [div_le_div_iff₀ (by positivity) hN]
  -- (Nμ)² ≤ N(μ+μ²)·ΣI, so μ·N ≤ (1+μ)·ΣI (divide by Nμ when μ > 0)
  rcases hμ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  · have h1 : (N * μ) ^ 2 ≤ N * (μ + μ ^ 2) * ∑ h, I h :=
      hcs.trans (mul_le_mul_of_nonneg_right hsq hIsum)
    have h2 : N * μ * (N * μ) ≤ N * μ * ((1 + μ) * ∑ h, I h) := by nlinarith
    have h3 := le_of_mul_le_mul_left h2 (by positivity)
    linarith

/-! ## The two endpoints -/

/-- At `w ≤ U`: `Pr[X>0] ≤ 1/32`. -/
theorem nonempty_prob_le_low (P : GapParams) (Z : List Bool) (hw : Z.count true ≤ P.cap) :
    booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) ≤ 1 / 32 := by
  refine (nonempty_prob_le P Z).trans ?_
  have h1 : (32 * P.cap : ℝ) ≤ 2 ^ P.prefixBits := by exact_mod_cast P.thirtyTwo_cap_le
  have h2 : (Z.count true : ℝ) ≤ P.cap := by exact_mod_cast hw
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- At `w ≥ 4096U` (`U ≥ 1`): `Pr[X>0] ≥ 64/65`. -/
theorem nonempty_prob_ge_high (P : GapParams) (hU : 1 ≤ P.cap) (Z : List Bool)
    (hZ : Z.length ≤ 2 ^ P.labelBits) (hw : 4096 * P.cap ≤ Z.count true) :
    (64 : ℝ) / 65 ≤
      booleanMean (fun h : ToeplitzSeed P.labelBits => decide (selectedActive P h Z).Nonempty) := by
  refine le_trans ?_ (nonempty_prob_ge P Z hZ)
  set μ : ℝ := (1 / 2 ^ P.prefixBits) * Z.count true with hμ
  have h1 : (2 : ℝ) ^ P.prefixBits < 64 * P.cap := by exact_mod_cast P.two_pow_prefixBits_lt hU
  have h2 : (4096 * P.cap : ℝ) ≤ Z.count true := by exact_mod_cast hw
  have hμ64 : 64 ≤ μ := by
    rw [hμ, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have : (0 : ℝ) < P.cap := by exact_mod_cast hU
    nlinarith
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

end NearCubicWires.WireExponent3_5.Filters

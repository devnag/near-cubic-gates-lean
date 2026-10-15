import Proof.Wire_3_5.WalkCount
import Proof.Wire_3_5.BlockMoment

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N Q L : ℕ}

def Ecell (D : Cell N → ℝ) (S : Fin Q → Cell N) (c : Cell N) : ℝ := D c * ∑ j, yc N (S j) c

/-- The walk-sum moment `Σ_w Π_k E(cell_k(w))` (= `tr((EEᵀ)^{L/2})` for even `L`). -/
def walkMoment (hL : 0 < L) (D : Cell N → ℝ) (S : Fin Q → Cell N) : ℝ :=
  ∑ w : Fin L → Fin N, ∏ k, Ecell D S (cellOf hL w k)

/-- The fiber of sample index `j` under the position-to-sample map `α`. -/
def fiber (α : Fin L → Fin Q) (j : Fin Q) : Finset (Fin L) := univ.filter fun k => α k = j

/-- Step A: expansion over sample-index maps and factorization over fibers (independence). -/
theorem sum_walkMoment_eq (hL : 0 < L) (D : Cell N → ℝ) :
    ∑ S : Fin Q → Cell N, walkMoment hL D S =
      ∑ w : Fin L → Fin N, (∏ k, D (cellOf hL w k)) *
        ∑ α : Fin L → Fin Q, ∏ j, ∑ s : Cell N, ∏ k ∈ fiber α j, yc N s (cellOf hL w k) := by
  unfold walkMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  have h1 : ∀ S : Fin Q → Cell N, ∏ k, Ecell D S (cellOf hL w k) =
      (∏ k, D (cellOf hL w k)) * ∑ α : Fin L → Fin Q, ∏ k, yc N (S (α k)) (cellOf hL w k) := by
    intro S
    unfold Ecell
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_univ_sum]
    simp [Fintype.piFinset_univ]
  simp only [h1, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro α _
  exact sum_prod_fiber α (fun k s => yc N s (cellOf hL w k))

/-- `|y(s,c)| ≤ 1 + N²[s = c]`. -/
theorem abs_yc_le (s c : Cell N) : |yc N s c| ≤ 1 + (N : ℝ) ^ 2 * (if s = c then 1 else 0) := by
  unfold yc
  split_ifs
  · rw [mul_one, abs_le]; constructor <;> nlinarith [sq_nonneg (N : ℝ)]
  · simp

/-- Step B: per-fiber bound by the subset expansion (`Finset.prod_add`). -/
theorem fiber_sum_abs_le (F : Finset (Fin L)) (c : Fin L → Cell N) :
    |∑ s : Cell N, ∏ k ∈ F, yc N s (c k)| ≤
      ∑ T ∈ F.powerset, (N : ℝ) ^ (2 * T.card) * ((univ.filter fun s : Cell N => ∀ k ∈ T, s = c k).card : ℝ) := by
  calc |∑ s : Cell N, ∏ k ∈ F, yc N s (c k)| ≤ ∑ s : Cell N, ∏ k ∈ F, |yc N s (c k)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro s _; exact Finset.abs_prod _ _
    _ ≤ ∑ s : Cell N, ∏ k ∈ F, (1 + (N : ℝ) ^ 2 * (if s = c k then 1 else 0)) := by
        apply Finset.sum_le_sum; intro s _
        exact Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => abs_yc_le s (c k))
    _ = ∑ s : Cell N, ∑ T ∈ F.powerset, ∏ k ∈ T, ((N : ℝ) ^ 2 * (if s = c k then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro s _
        rw [show (fun k => 1 + (N : ℝ) ^ 2 * (if s = c k then 1 else 0)) =
            (fun k => (N : ℝ) ^ 2 * (if s = c k then 1 else 0) + 1) from funext fun k => add_comm _ _]
        rw [Finset.prod_add]
        apply Finset.sum_congr rfl; intro T _; simp
    _ = ∑ T ∈ F.powerset, (N : ℝ) ^ (2 * T.card) *
          ((univ.filter fun s : Cell N => ∀ k ∈ T, s = c k).card : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro T _
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]
        congr 1
        rw [Finset.prod_boole]
        split_ifs <;> simp

/-- Step C: a singleton fiber kills the whole product (centring). -/
theorem prod_fiber_eq_zero_of_singleton (α : Fin L → Fin Q) (c : Fin L → Cell N) (j : Fin Q) (k₀ : Fin L)
    (hj : fiber α j = {k₀}) :
    ∏ j', ∑ s : Cell N, ∏ k ∈ fiber α j', yc N s (c k) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hj]
  simpa using block_sum_singleton (N := N) (c k₀)

end NearCubicWires.WireExponent3_5.Shared

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N Q L : ℕ}

/-- `#{s : ∀ k ∈ T, s = c k}`. -/
def cnt (T : Finset (Fin L)) (c : Fin L → Cell N) : ℕ :=
  (univ.filter fun s : Cell N => ∀ k ∈ T, s = c k).card

theorem cnt_empty (c : Fin L → Cell N) : cnt ∅ c = N ^ 2 := by
  simp [cnt, Fintype.card_prod, Fintype.card_fin, sq]

theorem cnt_le_one (T : Finset (Fin L)) (hT : T.Nonempty) (c : Fin L → Cell N) : cnt T c ≤ 1 := by
  obtain ⟨k, hk⟩ := hT
  unfold cnt
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [ha k hk, hb k hk]

theorem cnt_eq_zero_of_not_const (T : Finset (Fin L)) (c : Fin L → Cell N)
    (h : ¬ ∀ k ∈ T, ∀ l ∈ T, c k = c l) : cnt T c = 0 := by
  unfold cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ hs; apply h; intro k hk l hl; rw [← hs k hk, ← hs l hl]

/-- The representative map of a choice of sub-blocks `T j ⊆ fiber α j`: the least element of the block. -/
noncomputable def repT (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L)) (k : Fin L) : Fin L :=
  if h : k ∈ T (α k) then (T (α k)).min' ⟨k, h⟩ else k

theorem repT_le (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L)) (k : Fin L) : repT α T k ≤ k := by
  unfold repT; split_ifs with h
  · exact Finset.min'_le _ _ h
  · exact le_refl _

theorem repT_le_of_mem (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L)) {k l : Fin L}
    (hk : k ∈ T (α k)) (hl : l ∈ T (α k)) : repT α T k ≤ l := by
  unfold repT; rw [dif_pos hk]; exact Finset.min'_le _ _ hl

theorem consistent_repT (hL : 0 < L) (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L)) (w : Fin L → Fin N)
    (hconst : ∀ j, ∀ k ∈ T j, ∀ l ∈ T j, cellOf hL w k = cellOf hL w l) :
    Consistent hL (repT α T) w := by
  intro k
  unfold repT; split_ifs with h
  · exact hconst (α k) k h _ (Finset.min'_mem _ _)
  · rfl

theorem card_fix_repT_le (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L)) (hTF : ∀ j, T j ⊆ fiber α j) :
    (univ.filter fun k => repT α T k = k).card ≤
      (univ.filter fun j => (T j).Nonempty).card + (L - ∑ j, (T j).card) := by
  classical
  have hsplit : (univ.filter fun k => repT α T k = k) ⊆
      (univ.filter fun k => k ∈ T (α k) ∧ repT α T k = k) ∪ (univ.filter fun k => k ∉ T (α k)) := by
    intro k hk; simp only [mem_filter, mem_univ, true_and, mem_union] at hk ⊢
    by_cases h : k ∈ T (α k)
    · left; exact ⟨h, hk⟩
    · right; exact h
  have h1 : (univ.filter fun k => k ∈ T (α k) ∧ repT α T k = k).card ≤
      (univ.filter fun j => (T j).Nonempty).card := by
    apply Finset.card_le_card_of_injOn α
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk ⊢
      exact ⟨k, hk.1⟩
    · intro k hk k' hk' hkk'
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk hk'
      have hk'in : k' ∈ T (α k) := by rw [hkk']; exact hk'.1
      have hkin : k ∈ T (α k') := by rw [← hkk']; exact hk.1
      apply le_antisymm
      · calc k = repT α T k := hk.2.symm
          _ ≤ k' := repT_le_of_mem α T hk.1 hk'in
      · calc k' = repT α T k' := hk'.2.symm
          _ ≤ k := repT_le_of_mem α T hk'.1 hkin
  have hin : (univ.filter fun k => k ∈ T (α k)).card = ∑ j, (T j).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := α) (t := univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    apply Finset.sum_congr rfl; intro j _
    congr 1; ext k
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h, rfl⟩; exact h
    · intro h
      have := hTF j h
      simp only [fiber, mem_filter, mem_univ, true_and] at this
      exact ⟨by rw [this]; exact h, this⟩
  have h2 : (univ.filter fun k => k ∉ T (α k)).card = L - ∑ j, (T j).card := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin L))) (fun k => k ∈ T (α k))
    rw [Finset.card_univ, Fintype.card_fin, hin] at this
    omega
  calc _ ≤ _ := Finset.card_le_card hsplit
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by rw [h2]; omega

end NearCubicWires.WireExponent3_5.Shared

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N Q L : ℕ}

theorem sum_fiber_card (α : Fin L → Fin Q) : ∑ j, (fiber α j).card = L := by
  have := Finset.card_eq_sum_card_fiberwise (f := α) (s := (univ : Finset (Fin L))) (t := univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

/-- Exponent bookkeeping: `Σ_j (|T_j| + [T_j = ∅]) ≤ L + #{j : fiber α j = ∅}`. -/
theorem sum_T_add_empty_le (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L)) (hTF : ∀ j, T j ⊆ fiber α j) :
    (∑ j, (T j).card) + (univ.filter fun j => T j = ∅).card ≤
      L + (univ.filter fun j => fiber α j = ∅).card := by
  classical
  have hper : ∀ j, (T j).card + (if T j = ∅ then 1 else 0) ≤
      (fiber α j).card + (if fiber α j = ∅ then 1 else 0) := by
    intro j
    have hsub := Finset.card_le_card (hTF j)
    by_cases hF : fiber α j = ∅
    · have : T j = ∅ := Finset.subset_empty.mp (hF ▸ hTF j)
      simp [this, hF]
    · have hFne : 1 ≤ (fiber α j).card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
      by_cases hT : T j = ∅
      · rw [if_pos hT, if_neg hF, hT, Finset.card_empty]; omega
      · rw [if_neg hT, if_neg hF]; omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin Q))) => hper j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  rw [Finset.card_filter, Finset.card_filter]
  have := sum_fiber_card α
  omega

/-- Per-`T` walk sum: `Σ_w Π_j N^{2|T_j|}·cnt(T_j) ≤ N^{2Q+2L+1−m}` with `m = #{j : fiber α j ≠ ∅}`. -/
theorem walk_sum_T_le (hL : 0 < L) (hN : 1 ≤ N) (α : Fin L → Fin Q) (T : Fin Q → Finset (Fin L))
    (hTF : ∀ j, T j ⊆ fiber α j) :
    ∑ w : Fin L → Fin N, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ)) ≤
      (N : ℝ) ^ (2 * Q + 2 * L + 1 - (univ.filter fun j => (fiber α j).Nonempty).card) := by
  classical
  set t := ∑ j, (T j).card
  set e := (univ.filter fun j => T j = ∅).card
  set fx := (univ.filter fun k => repT α T k = k).card
  set Const : (Fin L → Fin N) → Prop := fun w => ∀ j, ∀ k ∈ T j, ∀ l ∈ T j, cellOf hL w k = cellOf hL w l
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- (1) pointwise bound
  have hpt : ∀ w, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ)) ≤
      (N : ℝ) ^ (2 * t) * ((N : ℝ) ^ 2) ^ e * (if Const w then 1 else 0) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases hc : Const w
    · rw [if_pos hc, mul_one]
      calc ∏ j, (cnt (T j) (cellOf hL w) : ℝ) ≤ ∏ j, (if T j = ∅ then (N : ℝ) ^ 2 else 1) := by
            apply Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _)
            intro j _
            split_ifs with hT
            · rw [hT, cnt_empty]; push_cast; rfl
            · exact_mod_cast cnt_le_one (T j) (Finset.nonempty_iff_ne_empty.mpr hT) _
        _ = ((N : ℝ) ^ 2) ^ e := by rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    · rw [if_neg hc, mul_zero]
      simp only [Const, not_forall] at hc
      obtain ⟨j, k, hk, l, hl, hne⟩ := hc
      apply le_of_eq
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [cnt_eq_zero_of_not_const]; · simp
      intro h; exact hne (h k hk l hl)
  -- (2) the walk count
  have hcount : ∑ w : Fin L → Fin N, (if Const w then (1 : ℝ) else 0) ≤ (N : ℝ) ^ (1 + fx) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (univ.filter Const) ⊆ (univ.filter (Consistent (N := N) hL (repT α T))) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact consistent_repT hL α T w hw
    have := (Finset.card_le_card hsub).trans (card_consistent_le hL (repT α T) (repT_le α T))
    exact_mod_cast this
  -- (3) exponents
  have hfx := card_fix_repT_le α T hTF
  have hte := sum_T_add_empty_le α T hTF
  have hae : (univ.filter fun j => (T j).Nonempty).card + e = Q := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin Q))) (fun j => (T j).Nonempty)
    rw [Finset.card_univ, Fintype.card_fin] at this
    have heq : (univ.filter fun j => ¬(T j).Nonempty) = (univ.filter fun j => T j = ∅) := by
      ext j; simp [Finset.not_nonempty_iff_eq_empty]
    rw [heq] at this; exact this
  have hme : (univ.filter fun j => (fiber α j).Nonempty).card + (univ.filter fun j => fiber α j = ∅).card = Q := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin Q))) (fun j => (fiber α j).Nonempty)
    rw [Finset.card_univ, Fintype.card_fin] at this
    have heq : (univ.filter fun j => ¬(fiber α j).Nonempty) = (univ.filter fun j => fiber α j = ∅) := by
      ext j; simp [Finset.not_nonempty_iff_eq_empty]
    rw [heq] at this; exact this
  have htL : t ≤ L := by
    calc t ≤ ∑ j, (fiber α j).card := Finset.sum_le_sum fun j _ => Finset.card_le_card (hTF j)
      _ = L := sum_fiber_card α
  have hexp : 2 * t + 2 * e + (1 + fx) ≤
      2 * Q + 2 * L + 1 - (univ.filter fun j => (fiber α j).Nonempty).card := by omega
  calc ∑ w : Fin L → Fin N, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ))
      ≤ ∑ w : Fin L → Fin N, (N : ℝ) ^ (2 * t) * ((N : ℝ) ^ 2) ^ e * (if Const w then 1 else 0) :=
        Finset.sum_le_sum fun w _ => hpt w
    _ = (N : ℝ) ^ (2 * t) * ((N : ℝ) ^ 2) ^ e * ∑ w : Fin L → Fin N, (if Const w then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum]
    _ ≤ (N : ℝ) ^ (2 * t) * ((N : ℝ) ^ 2) ^ e * (N : ℝ) ^ (1 + fx) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (N : ℝ) ^ (2 * t + 2 * e + (1 + fx)) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hN1 hexp

end NearCubicWires.WireExponent3_5.Shared

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N Q L : ℕ}

/-- Per sample-index map `α` without singleton fibers: `Σ_w |Π_j B_j| ≤ 2^L·N^{2Q+2L+1−m(α)}`. -/
theorem sum_w_abs_B_le (hL : 0 < L) (hN : 1 ≤ N) (α : Fin L → Fin Q) :
    ∑ w : Fin L → Fin N, |∏ j, ∑ s : Cell N, ∏ k ∈ fiber α j, yc N s (cellOf hL w k)| ≤
      (2 : ℝ) ^ L * (N : ℝ) ^ (2 * Q + 2 * L + 1 - (univ.filter fun j => (fiber α j).Nonempty).card) := by
  classical
  set P := Fintype.piFinset fun j => (fiber α j).powerset
  have hB : ∀ w : Fin L → Fin N, |∏ j, ∑ s : Cell N, ∏ k ∈ fiber α j, yc N s (cellOf hL w k)| ≤
      ∑ T ∈ P, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ)) := by
    intro w
    rw [Finset.abs_prod]
    calc ∏ j, |∑ s : Cell N, ∏ k ∈ fiber α j, yc N s (cellOf hL w k)|
        ≤ ∏ j, ∑ T ∈ (fiber α j).powerset, (N : ℝ) ^ (2 * T.card) * (cnt T (cellOf hL w) : ℝ) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => fiber_sum_abs_le _ _)
      _ = ∑ T ∈ P, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ)) :=
          Finset.prod_univ_sum _ _
  have hP : (P.card : ℝ) = 2 ^ L := by
    simp only [P, Fintype.card_piFinset, Finset.card_powerset]
    rw [Finset.prod_pow_eq_pow_sum, sum_fiber_card]; push_cast; rfl
  calc ∑ w : Fin L → Fin N, |∏ j, ∑ s : Cell N, ∏ k ∈ fiber α j, yc N s (cellOf hL w k)|
      ≤ ∑ w : Fin L → Fin N, ∑ T ∈ P, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ)) :=
        Finset.sum_le_sum fun w _ => hB w
    _ = ∑ T ∈ P, ∑ w : Fin L → Fin N, ∏ j, ((N : ℝ) ^ (2 * (T j).card) * (cnt (T j) (cellOf hL w) : ℝ)) :=
        Finset.sum_comm
    _ ≤ ∑ _T ∈ P, (N : ℝ) ^ (2 * Q + 2 * L + 1 - (univ.filter fun j => (fiber α j).Nonempty).card) := by
        apply Finset.sum_le_sum; intro T hT
        apply walk_sum_T_le hL hN α T
        intro j
        have := (Fintype.mem_piFinset.mp hT) j
        exact Finset.mem_powerset.mp this
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hP]

theorem sum_walkMoment_le (hL : 0 < L) (hN : 1 ≤ N) (D : Cell N → ℝ) (hD : ∀ c, |D c| ≤ 1) :
    |∑ S : Fin Q → Cell N, walkMoment hL D S| ≤
      ∑ α ∈ (univ.filter fun α : Fin L → Fin Q => ∀ j, (fiber α j).card ≠ 1),
        (2 : ℝ) ^ L * (N : ℝ) ^ (2 * Q + 2 * L + 1 - (univ.filter fun j => (fiber α j).Nonempty).card) := by
  classical
  rw [sum_walkMoment_eq]
  set B : (Fin L → Fin N) → (Fin L → Fin Q) → ℝ :=
    fun w α => ∏ j, ∑ s : Cell N, ∏ k ∈ fiber α j, yc N s (cellOf hL w k)
  have hzero : ∀ w α, ¬(∀ j, (fiber α j).card ≠ 1) → B w α = 0 := by
    intro w α h
    push Not at h
    obtain ⟨j, hj⟩ := h
    obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hj
    exact prod_fiber_eq_zero_of_singleton α (cellOf hL w) j k₀ hk₀
  calc |∑ w, (∏ k, D (cellOf hL w k)) * ∑ α, B w α| ≤ ∑ w, ∑ α, |B w α| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [abs_mul]
        have hDp : |∏ k, D (cellOf hL w k)| ≤ 1 := by
          rw [Finset.abs_prod]; exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun k _ => hD _)
        calc |∏ k, D (cellOf hL w k)| * |∑ α, B w α| ≤ 1 * |∑ α, B w α| :=
              mul_le_mul_of_nonneg_right hDp (abs_nonneg _)
          _ ≤ ∑ α, |B w α| := by rw [one_mul]; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ α, ∑ w, |B w α| := Finset.sum_comm
    _ = ∑ α ∈ (univ.filter fun α : Fin L → Fin Q => ∀ j, (fiber α j).card ≠ 1), ∑ w, |B w α| := by
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun α : Fin L → Fin Q => ∀ j, (fiber α j).card ≠ 1)]
        have : ∑ α ∈ (univ.filter fun α : Fin L → Fin Q => ¬∀ j, (fiber α j).card ≠ 1), ∑ w, |B w α| = 0 := by
          apply Finset.sum_eq_zero; intro α hα
          have hα' := (Finset.mem_filter.mp hα).2
          apply Finset.sum_eq_zero; intro w _
          rw [hzero w α hα', abs_zero]
        rw [this, add_zero]
    _ ≤ _ := Finset.sum_le_sum fun α _ => sum_w_abs_B_le hL hN α

end NearCubicWires.WireExponent3_5.Shared

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

variable {N Q L : ℕ}

theorem card_nonempty_fibers (α : Fin L → Fin Q) :
    (univ.filter fun j => (fiber α j).Nonempty).card = (univ.image α).card := by
  congr 1; ext j
  simp only [mem_filter, mem_univ, true_and, mem_image, fiber, Finset.filter_nonempty_iff]

theorem two_mul_card_image_le (α : Fin L → Fin Q) (hα : ∀ j, (fiber α j).card ≠ 1) :
    2 * (univ.image α).card ≤ L := by
  classical
  calc 2 * (univ.image α).card = ∑ j ∈ univ.image α, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ univ.image α, (fiber α j).card := by
        apply Finset.sum_le_sum; intro j hj
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
        have hne : (fiber α j).Nonempty := ⟨k, by simp [fiber, hk]⟩
        have h1 := Finset.one_le_card.mpr hne
        have h2 := hα j
        omega
    _ ≤ ∑ j, (fiber α j).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = L := sum_fiber_card α

/-- `(Q/N)`-monotonicity of the exponent trade: `Q^m N^{X−m} ≤ Q^{m'} N^{X−m'}` for `m ≤ m' ≤ X`, `N ≤ Q`. -/
theorem pow_trade {m m' X : ℕ} (hmm : m ≤ m') (hX : m' ≤ X) (hNQ : N ≤ Q) :
    (Q : ℝ) ^ m * (N : ℝ) ^ (X - m) ≤ (Q : ℝ) ^ m' * (N : ℝ) ^ (X - m') := by
  have e1 : X - m = (m' - m) + (X - m') := by omega
  have e2 : m' = m + (m' - m) := by omega
  rw [e1, pow_add]; conv_rhs => rw [e2, pow_add]
  have hNQ' : (N : ℝ) ≤ Q := by exact_mod_cast hNQ
  have h := pow_le_pow_left₀ (Nat.cast_nonneg N) hNQ' (m' - m)
  calc (Q : ℝ) ^ m * ((N : ℝ) ^ (m' - m) * (N : ℝ) ^ (X - m'))
      = (Q : ℝ) ^ m * (N : ℝ) ^ (m' - m) * (N : ℝ) ^ (X - m') := by ring
    _ ≤ (Q : ℝ) ^ m * (Q : ℝ) ^ (m' - m) * (N : ℝ) ^ (X - m') := by gcongr
    _ = _ := by rw [← e2]

theorem sum_walkMoment_le_explicit (hL : 0 < L) (hN : 1 ≤ N) (hNQ : N ≤ Q) (D : Cell N → ℝ)
    (hD : ∀ c, |D c| ≤ 1) :
    |∑ S : Fin Q → Cell N, walkMoment hL D S| ≤
      (2 : ℝ) ^ L * ((L / 2 + 1 : ℕ) : ℝ) * (L : ℝ) ^ L * (Q : ℝ) ^ (L / 2) *
        (N : ℝ) ^ (2 * Q + 2 * L + 1 - L / 2) := by
  classical
  set X := 2 * Q + 2 * L + 1
  refine (sum_walkMoment_le hL hN D hD).trans ?_
  simp only [card_nonempty_fibers]
  -- group by the image set
  set A := univ.filter fun α : Fin L → Fin Q => ∀ j, (fiber α j).card ≠ 1
  set Ss := (univ : Finset (Finset (Fin Q))).filter fun S => 2 * S.card ≤ L
  have hmaps : ∀ α ∈ A, univ.image α ∈ Ss := by
    intro α hα
    simp only [Ss, mem_filter, mem_univ, true_and]
    exact two_mul_card_image_le α (mem_filter.mp hα).2
  have hstep1 : ∑ α ∈ A, (2 : ℝ) ^ L * (N : ℝ) ^ (X - (univ.image α).card) =
      ∑ S ∈ Ss, ∑ α ∈ A.filter (fun α => univ.image α = S), (2 : ℝ) ^ L * (N : ℝ) ^ (X - S.card) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro α hα
    rw [(mem_filter.mp hα).2]
  have hcount : ∀ S : Finset (Fin Q), (A.filter (fun α => univ.image α = S)).card ≤ S.card ^ L := by
    intro S
    calc (A.filter (fun α => univ.image α = S)).card
        ≤ (Fintype.piFinset fun _ : Fin L => S).card := by
          apply Finset.card_le_card; intro α hα
          have himg := (mem_filter.mp hα).2
          rw [Fintype.mem_piFinset]; intro k
          rw [← himg]; exact Finset.mem_image_of_mem α (mem_univ k)
      _ = S.card ^ L := by simp
  have hstep2 : ∑ S ∈ Ss, ∑ α ∈ A.filter (fun α => univ.image α = S), (2 : ℝ) ^ L * (N : ℝ) ^ (X - S.card)
      ≤ ∑ S ∈ Ss, (2 : ℝ) ^ L * (L : ℝ) ^ L * (N : ℝ) ^ (X - S.card) := by
    apply Finset.sum_le_sum; intro S hS
    rw [Finset.sum_const, nsmul_eq_mul]
    have hSL : S.card ≤ L := by have := (mem_filter.mp hS).2; omega
    have h1 : ((A.filter (fun α => univ.image α = S)).card : ℝ) ≤ (L : ℝ) ^ L := by
      calc ((A.filter (fun α => univ.image α = S)).card : ℝ) ≤ ((S.card ^ L : ℕ) : ℝ) := by
            exact_mod_cast hcount S
        _ ≤ (L : ℝ) ^ L := by push_cast; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hSL) L
    calc ((A.filter (fun α => univ.image α = S)).card : ℝ) * ((2 : ℝ) ^ L * (N : ℝ) ^ (X - S.card))
        ≤ (L : ℝ) ^ L * ((2 : ℝ) ^ L * (N : ℝ) ^ (X - S.card)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  -- group subsets by size and use C(Q,s) ≤ Q^s, then the exponent trade up to s = L/2
  have hstep3 : ∑ S ∈ Ss, (2 : ℝ) ^ L * (L : ℝ) ^ L * (N : ℝ) ^ (X - S.card) ≤
      ∑ s ∈ Finset.range (L / 2 + 1), (2 : ℝ) ^ L * (L : ℝ) ^ L * ((Q : ℝ) ^ s * (N : ℝ) ^ (X - s)) := by
    have hmapsS : ∀ S ∈ Ss, S.card ∈ Finset.range (L / 2 + 1) := by
      intro S hS; have := (mem_filter.mp hS).2; rw [Finset.mem_range]; omega
    rw [← Finset.sum_fiberwise_of_maps_to hmapsS]
    apply Finset.sum_le_sum; intro s _
    calc ∑ S ∈ Ss.filter (fun S => S.card = s), (2 : ℝ) ^ L * (L : ℝ) ^ L * (N : ℝ) ^ (X - S.card)
        = ∑ S ∈ Ss.filter (fun S => S.card = s), (2 : ℝ) ^ L * (L : ℝ) ^ L * (N : ℝ) ^ (X - s) := by
          apply Finset.sum_congr rfl; intro S hS; rw [(mem_filter.mp hS).2]
      _ = ((Ss.filter (fun S => S.card = s)).card : ℝ) * ((2 : ℝ) ^ L * (L : ℝ) ^ L * (N : ℝ) ^ (X - s)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) ^ s * ((2 : ℝ) ^ L * (L : ℝ) ^ L * (N : ℝ) ^ (X - s)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hsub : Ss.filter (fun S => S.card = s) ⊆ Finset.powersetCard s univ := by
            intro S hS; rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, (mem_filter.mp hS).2⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this
          calc ((Ss.filter (fun S => S.card = s)).card : ℝ) ≤ ((Q.choose s : ℕ) : ℝ) := by exact_mod_cast this
            _ ≤ ((Q ^ s : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_pow Q s
            _ = (Q : ℝ) ^ s := by push_cast; rfl
      _ = _ := by ring
  have hstep4 : ∑ s ∈ Finset.range (L / 2 + 1), (2 : ℝ) ^ L * (L : ℝ) ^ L * ((Q : ℝ) ^ s * (N : ℝ) ^ (X - s)) ≤
      ∑ _s ∈ Finset.range (L / 2 + 1), (2 : ℝ) ^ L * (L : ℝ) ^ L * ((Q : ℝ) ^ (L / 2) * (N : ℝ) ^ (X - L / 2)) := by
    apply Finset.sum_le_sum; intro s hs
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hs' : s ≤ L / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    exact pow_trade hs' (by omega) hNQ
  calc _ = ∑ S ∈ Ss, ∑ α ∈ A.filter (fun α => univ.image α = S), (2 : ℝ) ^ L * (N : ℝ) ^ (X - S.card) := hstep1
    _ ≤ _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ _ := hstep4
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end NearCubicWires.WireExponent3_5.Shared

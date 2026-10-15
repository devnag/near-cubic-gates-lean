import Proof.Wire_3_5.ListDecoder
import Proof.Wire_3_5.ListOneHot

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters MvPolynomial
open Finset

/-- The data of a repaired count list: the output range `M`, the depth `J`, the windows `W_j`, and the nested hash's
level sets `𝓛_j` (`inLevel j i`). -/
structure ListData where
  /-- the states are `P_0, …, P_M` -/
  M : ℕ
  /-- the depth `J` -/
  J : ℕ
  /-- the windows `W_j` -/
  W : ℕ → ℕ
  /-- coordinate `i` lies in the level set `𝓛_j` -/
  inLevel : ℕ → ℕ → Bool

namespace ListData
variable (D : ListData)

def ell (j : ℕ) : ℕ := Nat.clog 2 (2 * D.W j + 1)

def levelCount (j : ℕ) (Z : List Bool) : ℕ :=
  ((Finset.range Z.length).filter fun i => Z.getD i false = true ∧ D.inLevel j i = true).card

def levelDelta (j : ℕ) (Z : List Bool) : ℤ := (D.levelCount j Z : ℤ) - 2 * (D.levelCount (j + 1) Z : ℤ)

def decoderBits (j : ℕ) (Z : List Bool) : Fin (D.ell j) → ZMod 2 :=
  fun h => bitF2 ((D.levelDelta j Z + D.W j).testBit h)

def levelDecoder (j : ℕ) (Z : List Bool) : ℤ → ZMod 2 :=
  residueDecoder (D.ell j) (D.W j) (D.decoderBits j Z)

def listStates (Z : List Bool) : ℕ → ZMod 2 :=
  repair D.M (recurAll D.M ((List.range D.J).map fun j => D.levelDecoder j Z))

def listReport (Z : List Bool) : ℕ :=
  ((List.range (D.M + 1)).find? fun s => decide (D.listStates Z s = 1)).getD 0

theorem listStates_exactlyOneHot (Z : List Bool) :
    ∃ s ≤ D.M, D.listStates Z s = 1 ∧ ∀ s' ≤ D.M, D.listStates Z s' = 1 → s' = s :=
  repair_exactlyOneHot D.M _ (recurAll_atMostOneHot D.M _ (by
    intro A hA
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hA
    exact residueDecoder_atMostOneHot _ _ _))

theorem listReport_le (Z : List Bool) : D.listReport Z ≤ D.M := by
  obtain ⟨s, hs, h1, _⟩ := D.listStates_exactlyOneHot Z
  unfold listReport
  cases hf : (List.range (D.M + 1)).find? fun s => decide (D.listStates Z s = 1) with
  | none =>
    exact absurd (List.find?_eq_none.mp hf s (List.mem_range.mpr (by omega))) (by simp [h1])
  | some r =>
    have := List.mem_range.mp (List.mem_of_find?_eq_some hf); simp only [Option.getD_some]; omega

theorem listStates_eq_one_iff (Z : List Bool) (s : ℕ) (hs : s ≤ D.M) :
    D.listStates Z s = 1 ↔ s = D.listReport Z := by
  obtain ⟨r, hr, h1, huniq⟩ := D.listStates_exactlyOneHot Z
  have hrep : D.listReport Z = r := by
    unfold listReport
    cases hf : (List.range (D.M + 1)).find? fun s => decide (D.listStates Z s = 1) with
    | none => exact absurd (List.find?_eq_none.mp hf r (List.mem_range.mpr (by omega))) (by simp [h1])
    | some r' =>
      have hr' := List.find?_some hf
      simp only [decide_eq_true_eq] at hr'
      have := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      simp only [Option.getD_some]
      exact huniq r' (by omega) hr'
  rw [hrep]
  exact ⟨fun h => huniq s hs h, fun h => h ▸ h1⟩

def Good (Z : List Bool) : Prop := D.levelCount D.J Z = 0 ∧ ∀ j < D.J, |D.levelDelta j Z| ≤ D.W j

theorem levelCount_le (j : ℕ) (Z : List Bool) : D.levelCount j Z ≤ Z.length := by
  unfold levelCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- `c_0 = w(Z)` when `𝓛_0` is everything. -/
theorem levelCount_zero (hL0 : ∀ i, D.inLevel 0 i = true) (Z : List Bool) : D.levelCount 0 Z = Z.count true := by
  rw [← card_activeSet]
  unfold levelCount activeSet
  congr 1; ext i; simp [hL0]

theorem two_mul_lt_two_pow_ell (j : ℕ) : 2 * D.W j < 2 ^ D.ell j := by
  have := Nat.le_pow_clog (b := 2) (by norm_num) (2 * D.W j + 1)
  unfold ell; omega

/-- On `|δ| ≤ W`, the decoder is exactly the indicator of `δ` (Lucas: its bits are the bits of `δ + W`). -/
theorem levelDecoder_good (j : ℕ) (Z : List Bool) (hδ : |D.levelDelta j Z| ≤ D.W j) (d : ℤ) :
    D.levelDecoder j Z d = if d = D.levelDelta j Z then 1 else 0 := by
  set δ := D.levelDelta j Z
  set W : ℤ := (D.W j : ℤ)
  have hH := D.two_mul_lt_two_pow_ell j
  have hHz : 2 * W < 2 ^ D.ell j := by simp only [W]; exact_mod_cast hH
  have hδ' := abs_le.mp hδ
  unfold levelDecoder residueDecoder decoderBits
  by_cases hd : d = δ
  · subst hd
    rw [if_pos ⟨by linarith [hδ'.1], by linarith [hδ'.2]⟩, if_pos rfl]
    apply Finset.prod_eq_one; intro h _
    have hnn : 0 ≤ δ + W := by linarith [hδ'.1]
    have : (δ + W).testBit h = (δ + W).toNat.testBit h := by
      conv_lhs => rw [← Int.toNat_of_nonneg hnn]
      rfl
    rw [this]; unfold bitF2; split_ifs <;> decide
  · rw [if_neg hd]
    split_ifs with hr
    · -- some bit differs, so one factor vanishes
      have hnn : 0 ≤ δ + W := by linarith [hδ'.1]
      have hne : (d + W).toNat ≠ (δ + W).toNat := by omega
      obtain ⟨i, hi⟩ : ∃ i, (d + W).toNat.testBit i ≠ (δ + W).toNat.testBit i := by
        by_contra hall; push Not at hall; exact hne (Nat.eq_of_testBit_eq hall)
      have hil : i < D.ell j := by
        by_contra hge; push Not at hge
        have h2 : 2 ^ D.ell j ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hge
        have h1 : (d + W).toNat < 2 ^ i := by
          have : ((d + W).toNat : ℤ) < 2 ^ D.ell j := by rw [Int.toNat_of_nonneg hr.1]; exact hr.2
          have : (d + W).toNat < 2 ^ D.ell j := by exact_mod_cast this
          omega
        have h3 : (δ + W).toNat < 2 ^ i := by
          have : ((δ + W).toNat : ℤ) < 2 ^ D.ell j := by rw [Int.toNat_of_nonneg hnn]; linarith [hδ'.2]
          have : (δ + W).toNat < 2 ^ D.ell j := by exact_mod_cast this
          omega
        exact hi (by rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h3])
      apply Finset.prod_eq_zero (i := ⟨i, hil⟩) (Finset.mem_univ _)
      have hbit : (δ + W).testBit i = (δ + W).toNat.testBit i := by
        conv_lhs => rw [← Int.toNat_of_nonneg hnn]
        rfl
      show bitF2 ((δ + W).testBit i) + 1 - (if (d + W).toNat.testBit i = true then 1 else 0) = 0
      rw [hbit]
      rcases Bool.eq_false_or_eq_true ((d + W).toNat.testBit i) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true ((δ + W).toNat.testBit i) with h2 | h2
      · exact absurd (h1.trans h2.symm) hi
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
      · exact absurd (h1.trans h2.symm) hi
    · rfl

/-- The recurrence from level `j` down: the decoders of levels `j, …, J−1`. -/
def levelsFrom (j : ℕ) (Z : List Bool) : List (ℤ → ZMod 2) :=
  (List.range' j (D.J - j)).map fun j' => D.levelDecoder j' Z

theorem levelsFrom_zero (Z : List Bool) :
    D.levelsFrom 0 Z = (List.range D.J).map fun j => D.levelDecoder j Z := by
  simp [levelsFrom, List.range_eq_range']

theorem recurAll_levelsFrom (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (Z : List Bool) (hZ : Z.length ≤ D.M) (hgood : D.Good Z) :
    ∀ k j, D.J - j = k → ∀ s ≤ D.M, recurAll D.M (D.levelsFrom j Z) s =
      if (s : ℕ) = D.levelCount j Z then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro j hj s _
    have hjJ : D.J ≤ j := by omega
    have hempty : D.levelsFrom j Z = [] := by simp [levelsFrom, hj]
    rw [hempty]
    -- `c_j = 0` for `j ≥ J`
    have hc : D.levelCount j Z = 0 := by
      have h0 := hgood.1
      unfold levelCount at h0 ⊢
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0 ⊢
      intro i hi ⟨hz, hl⟩
      have : ∀ m, D.inLevel (D.J + m) i = true → D.inLevel D.J i = true := by
        intro m; induction m with
        | zero => simp
        | succ m ih => intro h; exact ih (hnest _ _ h)
      exact h0 hi ⟨hz, this (j - D.J) (by rwa [Nat.add_sub_cancel' hjJ])⟩
    simp [recurAll, hc]
  | succ k ih =>
    intro j hj s hs
    have hjJ : j < D.J := by omega
    have hcons : D.levelsFrom j Z = D.levelDecoder j Z :: D.levelsFrom (j + 1) Z := by
      simp only [levelsFrom]
      rw [show D.J - j = (D.J - (j + 1)) + 1 by omega, List.range'_succ]
      rfl
    rw [hcons]
    simp only [recurAll, recurStep]
    have hchild := ih (j + 1) (by omega)
    have hcle : D.levelCount (j + 1) Z ≤ D.M := (D.levelCount_le _ Z).trans hZ
    rw [Finset.sum_eq_single (D.levelCount (j + 1) Z)]
    · rw [hchild _ hcle, if_pos rfl, one_mul, D.levelDecoder_good j Z (hgood.2 j hjJ)]
      unfold levelDelta
      congr 1
      apply propext; constructor <;> intro h <;> omega
    · intro t ht htne
      rw [hchild t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)), if_neg htne, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hcle)) h

theorem listReport_eq_count (hL0 : ∀ i, D.inLevel 0 i = true)
    (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (Z : List Bool) (hZ : Z.length ≤ D.M) (hgood : D.Good Z) : D.listReport Z = Z.count true := by
  have hw : Z.count true ≤ D.M := (List.count_le_length ..).trans hZ
  have hrec := D.recurAll_levelsFrom hnest Z hZ hgood D.J 0 (by omega)
  rw [D.levelsFrom_zero, D.levelCount_zero hL0] at hrec
  have hstate : D.listStates Z (Z.count true) = 1 := by
    unfold listStates repair
    split_ifs with h0
    · rw [Finset.sum_eq_zero]
      · simp
      · intro s hs
        have hs0 := (Finset.mem_erase.mp hs).1
        rw [hrec s (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hs).2)), if_neg (by omega)]
    · rw [hrec _ hw, if_pos rfl]
  exact ((D.listStates_eq_one_iff Z _ hw).mp hstate).symm

end ListData

end NearCubicWires.WireExponent3_5.Lists

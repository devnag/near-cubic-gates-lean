import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open Finset

/-- A vector with at most one entry `1` on `[0, M]` (in `ZMod 2` every other entry is `0`). -/
def AtMostOneHot (M : ℕ) (P : ℕ → ZMod 2) : Prop :=
  ∀ s ≤ M, ∀ s' ≤ M, P s = 1 → P s' = 1 → s = s'

/-- A decoder on `ℤ` with at most one `1`. -/
def AtMostOneHotZ (A : ℤ → ZMod 2) : Prop := ∀ d d', A d = 1 → A d' = 1 → d = d'

theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

def residueDecoder (ℓ : ℕ) (W : ℤ) (G : Fin ℓ → ZMod 2) (d : ℤ) : ZMod 2 :=
  if 0 ≤ d + W ∧ d + W < 2 ^ ℓ then
    ∏ h : Fin ℓ, (G h + 1 - (if (d + W).toNat.testBit h then 1 else 0))
  else 0

theorem residueDecoder_atMostOneHot (ℓ : ℕ) (W : ℤ) (G : Fin ℓ → ZMod 2) :
    AtMostOneHotZ (residueDecoder ℓ W G) := by
  intro d d' hd hd'
  unfold residueDecoder at hd hd'
  split_ifs at hd hd' with h1 h2
  · have key : ∀ (x : ℕ), (∏ h : Fin ℓ, (G h + 1 - (if x.testBit h then 1 else 0)) = (1 : ZMod 2)) →
        ∀ h : Fin ℓ, (x.testBit h = true ↔ G h = 1) := by
      intro x hx h
      have hfac : G h + 1 - (if x.testBit h then 1 else 0) = (1 : ZMod 2) := by
        by_contra hne
        have h0 : G h + 1 - (if x.testBit h then 1 else 0) = (0 : ZMod 2) :=
          (zmod2_eq_zero_or_one _).resolve_right hne
        rw [Finset.prod_eq_zero (Finset.mem_univ h) h0] at hx; exact zero_ne_one hx
      rcases zmod2_eq_zero_or_one (G h) with hg | hg <;> cases hb : x.testBit h <;>
        simp_all
    have hx := key _ hd; have hx' := key _ hd'
    have heq : (d + W).toNat = (d' + W).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < ℓ
      · have a := hx ⟨i, hi⟩; have b := hx' ⟨i, hi⟩
        cases hA : (d + W).toNat.testBit i <;> cases hB : (d' + W).toNat.testBit i <;> simp_all
      · have e : (((2 : ℕ) ^ ℓ : ℕ) : ℤ) = (2 : ℤ) ^ ℓ := by push_cast; ring
        have hA : (d + W).toNat < 2 ^ ℓ := by have := h1.2; omega
        have hB : (d' + W).toNat < 2 ^ ℓ := by have := h2.2; omega
        have hle : 2 ^ ℓ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hlt1 : (d + W).toNat < 2 ^ i := lt_of_lt_of_le hA hle
        have hlt2 : (d' + W).toNat < 2 ^ i := lt_of_lt_of_le hB hle
        rw [Nat.testBit_eq_false_of_lt hlt1, Nat.testBit_eq_false_of_lt hlt2]
    omega
  all_goals first | exact absurd hd zero_ne_one | exact absurd hd' zero_ne_one

def recurStep (M : ℕ) (A : ℤ → ZMod 2) (child : ℕ → ZMod 2) (s : ℕ) : ZMod 2 :=
  ∑ t ∈ range (M + 1), child t * A ((s : ℤ) - 2 * t)

theorem recurStep_atMostOneHot (M : ℕ) (A : ℤ → ZMod 2) (hA : AtMostOneHotZ A) (child : ℕ → ZMod 2)
    (hc : AtMostOneHot M child) : AtMostOneHot M (recurStep M A child) := by
  have single : ∀ s, recurStep M A child s = 1 →
      ∃ t ≤ M, child t = 1 ∧ A ((s : ℤ) - 2 * t) = 1 := by
    intro s hs
    by_contra hno
    push Not at hno
    apply zero_ne_one (α := ZMod 2)
    rw [← hs]; unfold recurStep
    symm; apply Finset.sum_eq_zero; intro t ht
    have htM : t ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rcases zmod2_eq_zero_or_one (child t) with h0 | h1
    · rw [h0, zero_mul]
    · rcases zmod2_eq_zero_or_one (A ((s : ℤ) - 2 * t)) with a0 | a1
      · rw [a0, mul_zero]
      · exact absurd a1 (hno t htM h1)
  intro s hs s' hs' h h'
  obtain ⟨t, ht, hct, hat⟩ := single s h
  obtain ⟨t', ht', hct', hat'⟩ := single s' h'
  have htt : t = t' := hc t ht t' ht' hct hct'
  subst htt
  have := hA _ _ hat hat'
  omega

def recurAll (M : ℕ) : List (ℤ → ZMod 2) → (ℕ → ZMod 2)
  | [] => fun s => if s = 0 then 1 else 0
  | A :: rest => recurStep M A (recurAll M rest)

theorem recurAll_atMostOneHot (M : ℕ) (As : List (ℤ → ZMod 2)) (hAs : ∀ A ∈ As, AtMostOneHotZ A) :
    AtMostOneHot M (recurAll M As) := by
  induction As with
  | nil =>
    intro s _ s' _ h h'
    simp only [recurAll] at h h'
    split_ifs at h h' with h1 h2 <;> simp_all
  | cons A rest ih =>
    exact recurStep_atMostOneHot M A (hAs A (List.mem_cons_self ..))
      _ (ih fun B hB => hAs B (List.mem_cons_of_mem _ hB))

def repair (M : ℕ) (P : ℕ → ZMod 2) (s : ℕ) : ZMod 2 :=
  if s = 0 then 1 + ∑ s' ∈ (range (M + 1)).erase 0, P s' else P s

theorem repair_exactlyOneHot (M : ℕ) (P : ℕ → ZMod 2) (hP : AtMostOneHot M P) :
    ∃ s ≤ M, repair M P s = 1 ∧ ∀ s' ≤ M, repair M P s' = 1 → s' = s := by
  by_cases hex : ∃ s ∈ (range (M + 1)).erase 0, P s = 1
  · obtain ⟨s, hs, hPs⟩ := hex
    have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have hsM : s ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hs).2)
    have hsum : ∑ s' ∈ (range (M + 1)).erase 0, P s' = 1 := by
      rw [Finset.sum_eq_single s]
      · exact hPs
      · intro b hb hbs
        rcases zmod2_eq_zero_or_one (P b) with h0 | h1
        · exact h0
        · exact absurd (hP b (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hb).2)) s hsM h1 hPs) hbs
      · intro h; exact absurd hs h
    refine ⟨s, hsM, by simp [repair, hs0, hPs], ?_⟩
    intro s' hs' h'
    by_cases h0 : s' = 0
    · subst h0; simp only [repair, if_true, hsum] at h'; exact absurd h' (by decide)
    · simp only [repair, h0, if_false] at h'; exact hP s' hs' s hsM h' hPs
  · push Not at hex
    have hsum : ∑ s' ∈ (range (M + 1)).erase 0, P s' = 0 := by
      apply Finset.sum_eq_zero; intro s hs
      exact (zmod2_eq_zero_or_one (P s)).resolve_right (hex s hs)
    refine ⟨0, Nat.zero_le _, by simp [repair, hsum], ?_⟩
    intro s' hs' h'
    by_contra h0
    simp only [repair, h0, if_false] at h'
    exact hex s' (Finset.mem_erase.mpr ⟨h0, Finset.mem_range.mpr (Nat.lt_succ_of_le hs')⟩) h'

theorem repaired_list_exactlyOneHot (M : ℕ) (levels : List (Σ ℓ : ℕ, ℤ × (Fin ℓ → ZMod 2))) :
    ∃ s ≤ M, repair M (recurAll M (levels.map fun L => residueDecoder L.1 L.2.1 L.2.2)) s = 1 ∧
      ∀ s' ≤ M, repair M (recurAll M (levels.map fun L => residueDecoder L.1 L.2.1 L.2.2)) s' = 1 → s' = s :=
  repair_exactlyOneHot M _ (recurAll_atMostOneHot M _ (by
    intro A hA
    obtain ⟨L, _, rfl⟩ := List.mem_map.mp hA
    exact residueDecoder_atMostOneHot L.1 L.2.1 L.2.2))

end NearCubicWires.WireExponent3_5.Shared

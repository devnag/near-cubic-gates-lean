import Proof.Wire_3_5.OutMachineIface

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Val
open NearCubicWires.WireExponent3_5.FinalPass.Out

theorem stripStep_fix (a b : ℕ) (h : ¬ (a % 2 = 0 ∧ b % 2 = 0)) : stripStep (a, b) = (a, b) := by
  simp [stripStep, h]

theorem iterate_fix {α : Type} (f : α → α) (x : α) (h : f x = x) : ∀ k, f^[k] x = x
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply, h, iterate_fix f x h k]

theorem strip_gen : ∀ (k a b : ℕ), ∃ j, a = (stripStep^[k] (a, b)).1 * 2 ^ j ∧ b = (stripStep^[k] (a, b)).2 * 2 ^ j ∧
    (j = k ∨ (stripStep^[k] (a, b)).1 % 2 = 1 ∨ (stripStep^[k] (a, b)).2 % 2 = 1)
  | 0, a, b => ⟨0, by simp, by simp, Or.inl rfl⟩
  | k + 1, a, b => by
    by_cases h : a % 2 = 0 ∧ b % 2 = 0
    · have e : stripStep (a, b) = (a / 2, b / 2) := by simp [stripStep, h]
      obtain ⟨j, h1, h2, h3⟩ := strip_gen k (a / 2) (b / 2)
      refine ⟨j + 1, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, e, pow_succ, ← Nat.mul_assoc, ← h1]; omega
      · rw [Function.iterate_succ_apply, e, pow_succ, ← Nat.mul_assoc, ← h2]; omega
      · rw [Function.iterate_succ_apply, e]; omega
    · rw [Function.iterate_succ_apply, stripStep_fix a b h, iterate_fix stripStep (a, b) (stripStep_fix a b h)]
      refine ⟨0, by simp, by simp, Or.inr ?_⟩
      simp only
      omega

/-- **P1's values**: `num = a·2^j`, `den = b·2^j`, `a` or `b` odd, `0 < b`. -/
theorem strip_spec (W num den : ℕ) (hd : 0 < den) (hdW : den < 2 ^ W) :
    ∃ j, num = (strip W num den).1 * 2 ^ j ∧ den = (strip W num den).2 * 2 ^ j ∧
      ((strip W num den).1 % 2 = 1 ∨ (strip W num den).2 % 2 = 1) ∧ 0 < (strip W num den).2 := by
  obtain ⟨j, h1, h2, h3⟩ := strip_gen W num den
  have hb : 0 < (strip W num den).2 := by
    rcases Nat.eq_zero_or_pos (strip W num den).2 with h | h
    · unfold strip at h; rw [h2, h] at hd; simp at hd
    · exact h
  refine ⟨j, h1, h2, ?_, hb⟩
  rcases h3 with h3 | h3
  · have : 2 ^ j ≤ den := by
      unfold strip at hb; rw [h2]; exact Nat.le_mul_of_pos_left _ hb
    rw [h3] at this
    omega
  · exact h3

theorem stripStep_le (p : ℕ × ℕ) : (stripStep p).1 ≤ p.1 ∧ (stripStep p).2 ≤ p.2 := by
  unfold stripStep; split_ifs <;> simp <;> omega

theorem strip_le : ∀ (k : ℕ) (p : ℕ × ℕ), (stripStep^[k] p).1 ≤ p.1 ∧ (stripStep^[k] p).2 ≤ p.2
  | 0, p => ⟨le_rfl, le_rfl⟩
  | k + 1, p => by
    rw [Function.iterate_succ_apply]
    have h1 := strip_le k (stripStep p)
    have h2 := stripStep_le p
    omega

theorem oddPart_gen : ∀ (k u : ℕ), ∃ i, u = oddStep^[k] u * 2 ^ i ∧ (i = k ∨ oddStep^[k] u % 2 = 1)
  | 0, u => ⟨0, by simp, Or.inl rfl⟩
  | k + 1, u => by
    by_cases h : u % 2 = 0
    · have e : oddStep u = u / 2 := by simp [oddStep, h]
      obtain ⟨i, h1, h2⟩ := oddPart_gen k (u / 2)
      refine ⟨i + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, e, pow_succ, ← Nat.mul_assoc, ← h1]; omega
      · rw [Function.iterate_succ_apply, e]; omega
    · have e : oddStep u = u := by simp [oddStep, h]
      rw [Function.iterate_succ_apply, e, iterate_fix oddStep u e]
      exact ⟨0, by simp, Or.inr (by omega)⟩

/-- **P2's value**: `u = oddPart W u · 2^i`, `oddPart W u` odd. -/
theorem oddPart_spec (W u : ℕ) (hu : 0 < u) (huW : u < 2 ^ W) :
    ∃ i, u = oddPart W u * 2 ^ i ∧ oddPart W u % 2 = 1 := by
  obtain ⟨i, h1, h2⟩ := oddPart_gen W u
  refine ⟨i, h1, ?_⟩
  rcases h2 with h2 | h2
  · subst h2
    have hp : 0 < oddStep^[i] u := by
      rcases Nat.eq_zero_or_pos (oddStep^[i] u) with h | h
      · rw [h1, h] at hu; simp at hu
      · exact h
    have : 2 ^ i ≤ u := by rw [h1]; exact Nat.le_mul_of_pos_left _ hp
    omega
  · exact h2

theorem oddStep_le (u : ℕ) : oddStep u ≤ u := by unfold oddStep; split_ifs <;> omega

theorem oddPart_le : ∀ (k u : ℕ), oddStep^[k] u ≤ u
  | 0, _ => le_rfl
  | k + 1, u => by
    rw [Function.iterate_succ_apply]
    exact (oddPart_le k (oddStep u)).trans (oddStep_le u)

theorem coprime_two (u : ℕ) (hu : u % 2 = 1) : Nat.Coprime 2 u := by
  unfold Nat.Coprime
  rw [Nat.gcd_rec, hu]
  rfl

/-- **P2's gcd**: the odd part of `b` against `a` has the gcd of `a` and `b` when one of them is odd. -/
theorem gcd_oddPart (a b o i : ℕ) (hab : a % 2 = 1 ∨ b % 2 = 1) (hb : b = o * 2 ^ i) :
    Nat.gcd o a = Nat.gcd a b := by
  rcases hab with ha | hb1
  · have hc : Nat.Coprime (2 ^ i) a := Nat.Coprime.pow_left i (coprime_two a ha)
    rw [hb, Nat.gcd_comm a, Nat.Coprime.gcd_mul_right_cancel o hc]
  · have hi : i = 0 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exact h
      · exfalso
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [hb, pow_succ] at hb1
        have : o * 2 ^ m * 2 % 2 = 0 := Nat.mul_mod_left _ _
        rw [← Nat.mul_assoc] at hb1
        omega
    subst hi
    rw [hb, pow_zero, Nat.mul_one, Nat.gcd_comm]

/-- **One Stein round** (`u` odd): if `v` is odd, order the pair and subtract; then halve `v`. -/
def steinStep (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 % 2 = 1 then (if p.2 < p.1 then (p.2, (p.1 - p.2) / 2) else (p.1, (p.2 - p.1) / 2))
  else (p.1, p.2 / 2)

theorem stein_inv (W u v : ℕ) (hu : u % 2 = 1) (huW : u < 2 ^ W) (hvW : v < 2 ^ W) :
    (steinStep (u, v)).1 % 2 = 1 ∧ (steinStep (u, v)).1 < 2 ^ W ∧ (steinStep (u, v)).2 < 2 ^ W := by
  unfold steinStep
  split_ifs with h1 h2
  · refine ⟨h1, hvW, ?_⟩
    have : (u - v) / 2 ≤ u := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    simp only; omega
  · refine ⟨hu, huW, ?_⟩
    have : (v - u) / 2 ≤ v := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    simp only; omega
  · refine ⟨hu, huW, ?_⟩
    have : v / 2 ≤ v := Nat.div_le_self _ _
    simp only; omega

theorem gcd_half (u m : ℕ) (hu : u % 2 = 1) : Nat.gcd u (2 * m) = Nat.gcd u m :=
  Nat.Coprime.gcd_mul_left_cancel_right m (coprime_two u hu)

theorem stein_gcd (u v : ℕ) (hu : u % 2 = 1) : Nat.gcd (steinStep (u, v)).1 (steinStep (u, v)).2 = Nat.gcd u v := by
  unfold steinStep
  split_ifs with h1 h2
  · simp only
    have he : u - v = 2 * ((u - v) / 2) := by omega
    rw [← gcd_half v _ h1, ← he, Nat.gcd_sub_self_right (by omega), Nat.gcd_comm]
  · simp only
    have he : v - u = 2 * ((v - u) / 2) := by omega
    rw [← gcd_half u _ hu, ← he, Nat.gcd_sub_self_right (by omega)]
  · simp only
    have he : v = 2 * (v / 2) := by omega
    rw [← gcd_half u _ hu, ← he]

theorem size_half (x : ℕ) (hx : 0 < x) : Nat.size (x / 2) < Nat.size x := by
  have h1 := Nat.lt_size_self x
  have h2 : 0 < Nat.size x := Nat.size_pos.2 hx
  have h3 : x / 2 < 2 ^ (Nat.size x - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.size x = m + 1 := ⟨Nat.size x - 1, by omega⟩
    rw [hm, pow_succ] at h1
    rw [hm, Nat.add_sub_cancel]
    omega
  have h4 := Nat.size_le.2 h3
  omega

/-- The potential drops by one per round while `v ≠ 0`. -/
theorem stein_size (u v : ℕ) (hv : 0 < v) :
    Nat.size (steinStep (u, v)).1 + Nat.size (steinStep (u, v)).2 < Nat.size u + Nat.size v := by
  unfold steinStep
  split_ifs with h1 h2
  · simp only
    have a1 := size_half (u - v) (by omega)
    have a2 := Nat.size_le_size (Nat.sub_le u v)
    omega
  · simp only
    rcases Nat.eq_zero_or_pos (v - u) with h | h
    · rw [h]; simp; exact Nat.size_pos.2 hv
    · have a1 := size_half (v - u) h
      have a2 := Nat.size_le_size (Nat.sub_le v u)
      omega
  · simp only
    have := size_half v hv
    omega

theorem stein_zero (u : ℕ) : steinStep (u, 0) = (u, 0) := by simp [steinStep]

theorem stein_iter_inv (W : ℕ) : ∀ (k u v : ℕ), u % 2 = 1 → u < 2 ^ W → v < 2 ^ W →
    (steinStep^[k] (u, v)).1 % 2 = 1 ∧ (steinStep^[k] (u, v)).1 < 2 ^ W ∧ (steinStep^[k] (u, v)).2 < 2 ^ W ∧
      Nat.gcd (steinStep^[k] (u, v)).1 (steinStep^[k] (u, v)).2 = Nat.gcd u v
  | 0, u, v, hu, huW, hvW => ⟨hu, huW, hvW, rfl⟩
  | k + 1, u, v, hu, huW, hvW => by
    obtain ⟨i1, i2, i3⟩ := stein_inv W u v hu huW hvW
    have ih := stein_iter_inv W k (steinStep (u, v)).1 (steinStep (u, v)).2 i1 i2 i3
    rw [Function.iterate_succ_apply]
    rw [← stein_gcd u v hu]
    exact ih

theorem stein_end : ∀ (k u v : ℕ), u % 2 = 1 → Nat.size u + Nat.size v ≤ k + 1 → (steinStep^[k] (u, v)).2 = 0
  | 0, u, v, hu, hs => by
    have : 0 < Nat.size u := Nat.size_pos.2 (by omega)
    have hv : Nat.size v = 0 := by omega
    simpa using Nat.size_eq_zero.1 hv
  | k + 1, u, v, hu, hs => by
    rcases Nat.eq_zero_or_pos v with hv | hv
    · subst hv; rw [iterate_fix steinStep (u, 0) (stein_zero u)]
    · rw [Function.iterate_succ_apply]
      have d := stein_size u v hv
      have hu' := (stein_inv (Nat.size u + Nat.size v) u v hu (by
        have := Nat.lt_size_self u; have := Nat.pow_le_pow_right (by decide : 0 < 2)
          (Nat.le_add_right (Nat.size u) (Nat.size v)); omega) (by
        have := Nat.lt_size_self v; have := Nat.pow_le_pow_right (by decide : 0 < 2)
          (Nat.le_add_left (Nat.size v) (Nat.size u)); omega)).1
      have e := stein_end k (steinStep (u, v)).1 (steinStep (u, v)).2 hu' (by omega)
      rwa [Prod.mk.eta] at e

/-- **P3's value**: `2W` Stein rounds from an odd `u` and `v` below `2^W` end at `(gcd u v, 0)`. -/
theorem stein_spec (W u v : ℕ) (hu : u % 2 = 1) (huW : u < 2 ^ W) (hvW : v < 2 ^ W) :
    steinStep^[2 * W] (u, v) = (Nat.gcd u v, 0) := by
  have hsu : Nat.size u ≤ W := Nat.size_le.2 huW
  have hsv : Nat.size v ≤ W := Nat.size_le.2 hvW
  have h0 := stein_end (2 * W) u v hu (by omega)
  have hg := (stein_iter_inv W (2 * W) u v hu huW hvW).2.2.2
  rw [h0, Nat.gcd_zero_right] at hg
  ext
  · exact hg
  · exact h0

/-! ## The reduced rational -/

/-- **The reduced pair has the value of `Num/Den`**. -/
theorem reduce_eq (num den a b j : ℕ) (hn : num = a * 2 ^ j) (hd : den = b * 2 ^ j) (hb : 0 < b) :
    ((a / Nat.gcd a b : ℕ) : ℚ) / ((b / Nat.gcd a b : ℕ) : ℚ) = (num : ℚ) / den := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb
  have hgq : ((Nat.gcd a b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpq : ((2 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Nat.cast_div (Nat.gcd_dvd_left a b) hgq, Nat.cast_div (Nat.gcd_dvd_right a b) hgq, hn, hd]
  push_cast
  field_simp

end NearCubicWires.WireExponent3_5.FinalPass.Out.Val

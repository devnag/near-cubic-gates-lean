import SourceAdapters.Routing.TranslationBits
import Mathlib.Data.Nat.Find

/-! The literal carry cases cover every column and force a single column value.-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.RoutingPolynomial

theorem low_ones (c t : ℕ) (h : ∀ i < t, c.testBit i = true) :
    c % 2^t = 2^t - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < t
  · simp [hi, h i hi]
  · simp [hi]

theorem columnCase_exists (q : ℕ) (hq : 0 < q) (c : ℕ) :
    ∃ t, ColumnCase q t c := by
  classical
  by_cases h : ∃ t, t+1 < q ∧ c.testBit t = false
  · let t := Nat.find h
    have ht : t+1 < q ∧ c.testBit t = false := Nat.find_spec h
    refine ⟨t, by omega, low_ones c t ?_, fun _ => ht.2⟩
    intro i hi
    have hn : ¬ (i+1 < q ∧ c.testBit i = false) := Nat.find_min h hi
    have hiq : i+1 < q := by omega
    cases hb : c.testBit i
    · exact False.elim (hn ⟨hiq,hb⟩)
    · rfl
  · refine ⟨q-1, by omega, low_ones c (q-1) ?_, ?_⟩
    · intro i hi
      have hiq : i+1 < q := by omega
      cases hb : c.testBit i
      · exact False.elim (h ⟨i,hiq,hb⟩)
      · rfl
    · intro hn
      omega

/-- Equal cyclic neighbors imply that every column has the same value. -/
theorem cyclic_constant {R : Type*} (N : ℕ) (hN : 0 < N) (f : Fin N → R)
    (h : ∀ c : Fin N, f c = f ⟨(c.val+1)%N, Nat.mod_lt _ hN⟩) :
    ∀ c c', f c = f c' := by
  have hz : ∀ n (hn : n < N), f ⟨n,hn⟩ = f ⟨0,hN⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      have hh := h ⟨n,hn'⟩
      have hh' : f ⟨n,hn'⟩ = f ⟨n+1,hn⟩ := by
        simpa only [Nat.mod_eq_of_lt hn] using hh
      exact hh'.symm.trans (ih hn')
  intro c c'
  exact (hz c.val c.isLt).trans (hz c'.val c'.isLt).symm

/-- The zero-width column block is a singleton; positive widths are covered
by the carry cases, including the last-column wraparound case. -/
theorem column_cases_constant {R : Type*} (q : ℕ) (f : Fin (2^q) → R)
    (h : ∀ t (c : Fin (2^q)), ColumnCase q t c.val →
      f c = f ⟨(c.val+1)%(2^q), Nat.mod_lt _ (Nat.two_pow_pos q)⟩) :
    ∀ c c', f c = f c' := by
  by_cases hq : q=0
  · subst q
    intro c c'
    have hc : c=c' := by
      apply Fin.ext
      have := c.isLt
      have := c'.isLt
      norm_num at *
    rw [hc]
  · apply cyclic_constant (2^q) (Nat.two_pow_pos q) f
    intro c
    obtain ⟨t,ht⟩ := columnCase_exists q (by omega) c.val
    exact h t c ht

theorem column_mask_iff (q t c : ℕ) (ht : t < q) :
    c &&& (if t+1<q then 2^(t+1)-1 else 2^t-1) =
      (2^t-1) &&& (if t+1<q then 2^(t+1)-1 else 2^t-1) ↔
    ColumnCase q t c := by
  have hp := Nat.two_pow_pos t
  by_cases hn : t+1 < q
  · have hsmall : 2^t-1 < 2^(t+1) := by
      have hpow : 2^t < 2^(t+1) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    simp only [if_pos hn, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsmall]
    constructor
    · intro hc
      refine ⟨ht, ?_, fun _ => ?_⟩
      · have hm := congrArg (fun n => n % 2^t) hc
        rw [pow_succ, Nat.mod_mul_right_mod] at hm
        simpa only [Nat.mod_eq_of_lt (show 2^t-1 < 2^t by omega)] using hm
      · have hb := congrArg (fun n => n.testBit t) hc
        simpa [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one] using hb
    · intro hc
      exact LayoutFacts.mod_next_of_bit_false t c hc.2.1 (hc.2.2 hn)
  · simp only [if_neg hn, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (show 2^t-1 < 2^t by omega)]
    exact ⟨fun hc => ⟨ht,hc,fun hh => False.elim (hn hh)⟩, fun hc => hc.2.1⟩

theorem columnCase_unique {q t t' c : ℕ} (h : ColumnCase q t c)
    (h' : ColumnCase q t' c) : t=t' := by
  have not_lt {u v : ℕ} (hu : ColumnCase q u c) (hv : ColumnCase q v c) : ¬ u<v := by
    intro huv
    have hb := hu.2.2 (show u+1<q by have := hv.1; omega)
    have hm := congrArg (fun n => n.testBit u) hv.2.1
    simp [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, huv, hb] at hm
  exact Nat.le_antisymm (Nat.le_of_not_gt (not_lt h' h)) (Nat.le_of_not_gt (not_lt h h'))

end NearCubicGates.Adapters.Routing.RoutingPolynomial

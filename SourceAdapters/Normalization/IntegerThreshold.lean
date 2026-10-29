import SourceAdapters.Normalization.SmallDimension
import SourceAdapters.Normalization.FactorialBound
import Bindings.CTW26_Lemma3_2

/-!
# Bounded integer parameters for Boolean thresholds

For `lem:integer`, the affine dimension gives a factorial bound. In dimensions
at least three it is at most `m ^ m`; the segment and square supply the remaining
cases. The final statement uses real-valued Boolean inputs and inclusive ties.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Normalization

/-- Every positive-arity Boolean threshold has integer parameters bounded by `m ^ m`. -/
theorem exists_integer_threshold_pow {m : ℕ} (hm : 1 ≤ m) (w : Fin m → ℝ) (t : ℝ) :
    ∃ (a : Fin m → ℤ) (b : ℤ),
      (∀ x : Fin m → Bool,
        (t ≤ ∑ j, w j * (if x j then 1 else 0)) ↔
          (b ≤ ∑ j, a j * (if x j then 1 else 0))) ∧
      (∀ j, |a j| ≤ (m ^ m : ℕ)) ∧ |b| ≤ (m ^ m : ℕ) := by
  by_cases hm1 : m = 1
  · subst m
    obtain ⟨a, b, he, ha, hb⟩ := exists_integer_threshold_one (w 0) t
    refine ⟨fun _ => a, b, ?_, ?_, ?_⟩
    · intro x
      simpa using he (x 0)
    · intro j
      simpa using ha
    · simpa using hb
  by_cases hm2 : m = 2
  · subst m
    obtain ⟨a, b, c, he, ha, hb, hc⟩ := exists_integer_threshold_two (w 0) (w 1) t
    refine ⟨![a, b], c, ?_, ?_, ?_⟩
    · intro x
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using he (x 0) (x 1)
    · intro j
      fin_cases j <;> norm_num <;> assumption
    · norm_num
      exact hc
  obtain ⟨a, b, he, ha, hb⟩ := exists_integer_threshold w t
  have hbound : ((m + 1).factorial : ℤ) ≤ (m ^ m : ℕ) := by
    exact_mod_cast factorial_succ_le_pow (by omega : 3 ≤ m)
  refine ⟨a, b, he, ?_, ?_⟩
  · intro j
    apply le_trans _ hbound
    simpa only [Fintype.card_fin] using ha j
  · apply le_trans _ hbound
    simpa only [Fintype.card_fin] using hb

open NearCubicWires.Bindings.CTW26

/-- An integer representation on Boolean-valued inputs also represents the
same threshold on real inputs whose coordinates belong to `{0,1}`. -/
theorem equivalent_integer_gate {m : ℕ} (g : THRGate m) (a : Fin m → ℤ) (b : ℤ)
    (he : ∀ x : Fin m → Bool,
      (g.t ≤ ∑ j, g.w j * (if x j then 1 else 0)) ↔
        (b ≤ ∑ j, a j * (if x j then 1 else 0))) :
    Equivalent g ⟨fun j => (a j : ℝ), (b : ℝ)⟩ := by
  classical
  intro x hx
  let y : Fin m → Bool := fun j => decide (x j = 1)
  have hy (j : Fin m) : (if y j then (1 : ℝ) else 0) = x j := by
    rcases hx j with h | h <;> simp [y, h]
  unfold THRGate.output
  rw [I_eq_I_iff]
  have hcast : ((b ≤ ∑ j, a j * (if y j then 1 else 0)) ↔
      ((b : ℝ) ≤ ∑ j, (a j : ℝ) * (if y j then 1 else 0))) := by
    norm_cast
  simpa only [hy] using (he y).trans hcast

/-- Integer normalization of every positive-arity threshold, including its
threshold parameter and the inclusive comparison convention. `lem:integer`. -/
theorem integer_normalization :
    ∀ (m : ℕ), 1 ≤ m → ∀ g : THRGate m, ∃ h : THRGate m,
      Equivalent g h ∧ (∀ i, IsIntegerInRange (h.w i) (m ^ m)) ∧
        IsIntegerInRange h.t (m ^ m) := by
  intro m hm g
  obtain ⟨a, b, he, ha, hb⟩ := exists_integer_threshold_pow hm g.w g.t
  refine ⟨⟨fun j => (a j : ℝ), (b : ℝ)⟩, equivalent_integer_gate g a b he, ?_, ?_⟩
  · intro j
    exact ⟨a j, rfl, (abs_le.mp (ha j)).1, (abs_le.mp (ha j)).2⟩
  · exact ⟨b, rfl, (abs_le.mp hb).1, (abs_le.mp hb).2⟩

/-- The same normalization for every arity, using `0 ^ 0 = 1` for the constant
zero-input threshold. -/
theorem threshold_normalization : CTW26_Lemma3_2 := by
  intro m g
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ctw26_lemma3_2_at_zero g
  · exact integer_normalization m hm g

end NearCubicGates.Adapters.Normalization

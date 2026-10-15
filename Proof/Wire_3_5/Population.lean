import Proof.Wire_3_5.Influence

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires Finset

variable {n : ℕ}

/-- `c ⊕ 1_A`. -/
def xorSet (A : Finset (Fin n)) (c : BitInput n) : BitInput n := fun i => xor (c i) (decide (i ∈ A))

theorem xorSet_xorSet (A : Finset (Fin n)) (c : BitInput n) : xorSet A (xorSet A c) = c := by
  funext i; simp [xorSet]

theorem xorSet_empty (c : BitInput n) : xorSet ∅ c = c := by funext i; simp [xorSet]

def xorSetEquiv (A : Finset (Fin n)) : BitInput n ≃ BitInput n :=
  ⟨xorSet A, xorSet A, xorSet_xorSet A, xorSet_xorSet A⟩

theorem xorSet_insert {a : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) (c : BitInput n) :
    xorSet (insert a A) c = flipAt a (xorSet A c) := by
  funext i; by_cases h : i = a
  · subst h; simp [xorSet, flipAt, ha]
  · simp [xorSet, flipAt, h]

/-- Pivotal count of an arbitrary Boolean function (`2^n · Inf_i`). -/
def pivotCount (T : BitInput n → Bool) (i : Fin n) : ℕ :=
  (univ.filter fun x => T x ≠ T (flipAt i x)).card

theorem card_change_le (T : BitInput n → Bool) (A : Finset (Fin n)) :
    (univ.filter fun c => T (xorSet A c) ≠ T c).card ≤ ∑ i ∈ A, pivotCount T i := by
  induction A using Finset.induction_on with
  | empty => simp [xorSet_empty]
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha]
    have hsub : (univ.filter fun c => T (xorSet (insert a A) c) ≠ T c) ⊆
        (univ.filter fun c => T (flipAt a (xorSet A c)) ≠ T (xorSet A c)) ∪
          (univ.filter fun c => T (xorSet A c) ≠ T c) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, xorSet_insert ha] at hc ⊢
      by_contra h; push Not at h; exact hc (h.1.trans h.2)
    have hbij : (univ.filter fun c => T (flipAt a (xorSet A c)) ≠ T (xorSet A c)).card = pivotCount T a := by
      unfold pivotCount
      apply Finset.card_bij (fun c _ => xorSet A c)
      · intro c hc; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢; exact fun h => hc h.symm
      · intro c₁ _ c₂ _ h; simpa [xorSet_xorSet] using congrArg (xorSet A) h
      · intro x hx; refine ⟨xorSet A x, ?_, xorSet_xorSet A x⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, xorSet_xorSet] at hx ⊢
        exact fun h => hx h.symm
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ pivotCount T a + ∑ i ∈ A, pivotCount T i := by rw [hbij]; omega

def mixedDiffSet (T : BitInput n → Bool) (A B : Finset (Fin n)) (c : BitInput n) : ℤ :=
  bitZ (T (xorSet A (xorSet B c))) - bitZ (T (xorSet A c)) - bitZ (T (xorSet B c)) + bitZ (T c)

theorem card_mixed_ne_zero_le (T : BitInput n → Bool) (A B : Finset (Fin n)) :
    (univ.filter fun c => mixedDiffSet T A B c ≠ 0).card ≤ 2 * ∑ i ∈ A, pivotCount T i := by
  have hsub : (univ.filter fun c => mixedDiffSet T A B c ≠ 0) ⊆
      (univ.filter fun c => T (xorSet A c) ≠ T c) ∪
        (univ.filter fun c => T (xorSet A (xorSet B c)) ≠ T (xorSet B c)) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
    by_contra h; push Not at h; apply hc; unfold mixedDiffSet; rw [h.1, h.2]; ring
  have h2 : (univ.filter fun c => T (xorSet A (xorSet B c)) ≠ T (xorSet B c)).card =
      (univ.filter fun c => T (xorSet A c) ≠ T c).card := by
    apply Finset.card_bij (fun c _ => xorSet B c)
    · intro c hc; simpa using hc
    · intro c₁ _ c₂ _ h; simpa [xorSet_xorSet] using congrArg (xorSet B) h
    · intro x hx; exact ⟨xorSet B x, by simpa [xorSet_xorSet] using hx, xorSet_xorSet B x⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by rw [h2]; have := card_change_le T A; omega

theorem mixed_eq_zero_of_miss (T : BitInput n → Bool) (A B : Finset (Fin n))
    (hmiss : ∀ c, T (xorSet B c) = T c) (c : BitInput n) : mixedDiffSet T A B c = 0 := by
  have h1 : xorSet A (xorSet B c) = xorSet B (xorSet A c) := by
    funext i; simp only [xorSet]; cases c i <;> cases decide (i ∈ A) <;> cases decide (i ∈ B) <;> rfl
  unfold mixedDiffSet; rw [h1, hmiss, hmiss]; ring

/-- A normalized gate ignores flips outside its support. -/
theorem eval_xorSet_of_disjoint (g : NormalizedThresholdGate n) (B : Finset (Fin n))
    (hB : ∀ i ∈ B, g.weight i = 0) (c : BitInput n) : g.eval (xorSet B c) = g.eval c := by
  simp only [eval_eq_decide, gateScore]
  congr 2
  apply Finset.sum_congr rfl; intro i _
  by_cases h : i ∈ B
  · simp [hB i h]
  · simp [xorSet, h]

theorem sum_card_mixed_le {U V : Type} [Fintype U] [Fintype V] (g : NormalizedThresholdGate n)
    (A : U → Finset (Fin n)) (B : V → Finset (Fin n)) :
    (∑ u, ∑ v, (univ.filter fun c => mixedDiffSet g.eval (A u) (B v) c ≠ 0).card) ≤
      2 * (univ.filter fun v => ∃ i ∈ B v, g.weight i ≠ 0).card * ∑ u, ∑ i ∈ A u, pivotCount g.eval i := by
  have hpt : ∀ u v, (univ.filter fun c => mixedDiffSet g.eval (A u) (B v) c ≠ 0).card ≤
      (if ∃ i ∈ B v, g.weight i ≠ 0 then 1 else 0) * (2 * ∑ i ∈ A u, pivotCount g.eval i) := by
    intro u v
    split_ifs with h
    · rw [one_mul]; exact card_mixed_ne_zero_le _ _ _
    · push Not at h
      rw [zero_mul, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro c _; simp only [not_not]
      exact mixed_eq_zero_of_miss _ _ _ (eval_xorSet_of_disjoint g (B v) h) c
  calc (∑ u, ∑ v, (univ.filter fun c => mixedDiffSet g.eval (A u) (B v) c ≠ 0).card)
      ≤ ∑ u, ∑ v, (if ∃ i ∈ B v, g.weight i ≠ 0 then 1 else 0) * (2 * ∑ i ∈ A u, pivotCount g.eval i) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpt u v
    _ = (∑ v, (if ∃ i ∈ B v, g.weight i ≠ 0 then 1 else 0)) * ∑ u, (2 * ∑ i ∈ A u, pivotCount g.eval i) := by
        rw [Finset.sum_mul_sum, Finset.sum_comm]
    _ = 2 * (univ.filter fun v => ∃ i ∈ B v, g.weight i ≠ 0).card * ∑ u, ∑ i ∈ A u, pivotCount g.eval i := by
        rw [← Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_filter]; ring

end NearCubicWires.WireExponent3_5.Shared

import Proof.Wire_3_5.ValidityBridge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires NearCubicWires.ComponentwiseValidity

theorem bitAsReal_mem (b : Bool) : 0 ≤ bitAsReal b ∧ bitAsReal b ≤ 1 := by cases b <;> simp [bitAsReal]

/-- Pointwise clause error through rounding errors only. -/
theorem clauseValue_sub_le (n₁ n₂ : Bool) (x y bx by' : ℝ) (hbx : 0 ≤ bx ∧ bx ≤ 1) (hby : 0 ≤ by' ∧ by' ≤ 1) :
    |clauseValue n₁ n₂ x y - clauseValue n₁ n₂ bx by'| ≤ |x - bx| + |y - by'| + |x - bx| * |y - by'| := by
  unfold clauseValue literalValue
  cases n₁ <;> cases n₂ <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
  · rcases hbx with ⟨h1, h2⟩; rcases hby with ⟨h3, h4⟩
    rw [abs_le]; constructor <;>
    nlinarith [abs_nonneg (x - bx), abs_nonneg (y - by'), le_abs_self (x - bx), neg_abs_le (x - bx),
      le_abs_self (y - by'), neg_abs_le (y - by'), abs_mul_abs_self (x - bx), abs_mul (x - bx) (y - by'),
      le_abs_self ((x - bx) * (y - by')), neg_abs_le ((x - bx) * (y - by'))]

theorem uMean_marginal_le {C Ω : Type} [Fintype C] [Fintype Ω] (f : C → Fin 2 → Ω → ℝ)
    (hf : ∀ i j ω, 0 ≤ f i j ω) (j : Fin 2) :
    uMean (fun p : C × Ω => f p.1 j p.2) ≤ 2 * uMean (fun p : C × Fin 2 × Ω => f p.1 p.2.1 p.2.2) := by
  unfold uMean
  simp only [Fintype.card_prod, Fintype.card_fin]
  have hsum : ∑ p : C × Ω, f p.1 j p.2 ≤ ∑ p : C × Fin 2 × Ω, f p.1 p.2.1 p.2.2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply Finset.sum_le_sum; intro i _
    rw [Fintype.sum_prod_type]
    calc ∑ ω, f i j ω ≤ ∑ j' : Fin 2, ∑ ω, f i j' ω :=
          Finset.single_le_sum (f := fun j' => ∑ ω, f i j' ω)
            (fun j' _ => Finset.sum_nonneg fun ω _ => hf i j' ω) (Finset.mem_univ j)
      _ = _ := rfl
  rcases Nat.eq_zero_or_pos (Fintype.card C * Fintype.card Ω) with h0 | hpos
  · have h0' : ((Fintype.card C : ℝ) * Fintype.card Ω) = 0 := by exact_mod_cast h0
    have : ((Fintype.card C : ℝ) * (2 * Fintype.card Ω)) = 0 := by rw [mul_left_comm, h0', mul_zero]
    simp only [Nat.cast_mul, Nat.cast_ofNat, h0', this, div_zero, mul_zero, le_refl]
  · have hp : (0 : ℝ) < (Fintype.card C : ℝ) * Fintype.card Ω := by exact_mod_cast hpos
    push_cast
    rw [show ((Fintype.card C : ℝ) * (2 * Fintype.card Ω)) = 2 * ((Fintype.card C : ℝ) * Fintype.card Ω) by ring,
      mul_div_assoc', mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact div_le_div_of_nonneg_right hsum hp.le

/-- The corrected `tr:rounding`, sharp form: `≤ 2√(24v₀) + 24v₀` from the validity test alone. -/
theorem maskedRounding_sharp {Clause Ω : Type} [Fintype Clause] [Fintype Ω]
    (S : Clause → Fin 2 → Ω → ℝ) (con : Clause → Fin 2 → Ω → Option Bool)
    (neg : Clause → Fin 2 → Bool) (G : Clause → Fin 2 → Ω → Bool) (v₀ : ℝ) (hv : 0 < v₀)
    (hV : uMean (fun p : Clause × Fin 2 × Ω =>
        bitR (G p.1 p.2.1 p.2.2) * validityPenalty (con p.1 p.2.1 p.2.2) (S p.1 p.2.1 p.2.2)) ≤ 3 * v₀) :
    |uMean (fun p : Clause × Ω =>
        bitR (G p.1 0 p.2 && G p.1 1 p.2) *
          (clauseValue (neg p.1 0) (neg p.1 1) (S p.1 0 p.2) (S p.1 1 p.2) -
           clauseValue (neg p.1 0) (neg p.1 1)
             (bitAsReal (validityRound (con p.1 0 p.2) (S p.1 0 p.2)))
             (bitAsReal (validityRound (con p.1 1 p.2) (S p.1 1 p.2)))))| ≤
      2 * Real.sqrt (24 * v₀) + 24 * v₀ := by
  -- rounding errors
  set e : Fin 2 → Clause × Ω → ℝ := fun j p =>
    S p.1 j p.2 - bitAsReal (validityRound (con p.1 j p.2) (S p.1 j p.2)) with he
  set M : Clause × Ω → Bool := fun p => G p.1 0 p.2 && G p.1 1 p.2 with hM
  -- (1) masked second moment of each rounding error is at most 24 v₀
  have hsq : ∀ j : Fin 2, maskedMean M (fun p => e j p ^ 2) ≤ 24 * v₀ := by
    intro j
    have step1 : maskedMean M (fun p => e j p ^ 2) ≤
        uMean (fun p : Clause × Ω => bitR (G p.1 j p.2) * (4 * validityPenalty (con p.1 j p.2) (S p.1 j p.2))) := by
      apply uMean_mono; intro p
      have hpen := validityRound_distance_sq_le (con p.1 j p.2) (S p.1 j p.2)
      have hMG : bitR (M p) ≤ bitR (G p.1 j p.2) := by
        have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
        unfold bitR
        rcases hj j with rfl | rfl <;> simp only [hM] <;> cases G p.1 0 p.2 <;> cases G p.1 1 p.2 <;> simp
      have he2 : 0 ≤ e j p ^ 2 := sq_nonneg _
      calc bitR (M p) * e j p ^ 2 ≤ bitR (G p.1 j p.2) * e j p ^ 2 :=
            mul_le_mul_of_nonneg_right hMG he2
        _ ≤ _ := mul_le_mul_of_nonneg_left hpen (bitR_nonneg _)
    have step2 := uMean_marginal_le
      (fun i j' ω => bitR (G i j' ω) * (4 * validityPenalty (con i j' ω) (S i j' ω)))
      (fun i j' ω => mul_nonneg (bitR_nonneg _) (by
        have := validityRound_distance_sq_le (con i j' ω) (S i j' ω); nlinarith [sq_nonneg
          (S i j' ω - bitAsReal (validityRound (con i j' ω) (S i j' ω)))])) j
    have step3 : uMean (fun p : Clause × Fin 2 × Ω =>
        bitR (G p.1 p.2.1 p.2.2) * (4 * validityPenalty (con p.1 p.2.1 p.2.2) (S p.1 p.2.1 p.2.2))) =
        4 * uMean (fun p : Clause × Fin 2 × Ω =>
          bitR (G p.1 p.2.1 p.2.2) * validityPenalty (con p.1 p.2.1 p.2.2) (S p.1 p.2.1 p.2.2)) := by
      unfold uMean; rw [mul_div_assoc', Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro p _
      dsimp only; ring
    calc _ ≤ _ := step1
      _ ≤ _ := step2
      _ = 2 * (4 * _) := by rw [step3]
      _ ≤ 2 * (4 * (3 * v₀)) := by nlinarith [hV]
      _ = 24 * v₀ := by ring
  -- (2) first moments by masked Cauchy–Schwarz
  have hone : ∀ j : Fin 2, maskedMean M (fun p => |e j p|) ≤ Real.sqrt (24 * v₀) := by
    intro j
    have h := maskedMean_abs_mul_le M (e j) (fun _ => 1)
    simp only [mul_one, one_pow] at h
    have hM1 : maskedMean M (fun _ => (1 : ℝ)) ≤ 1 := by
      have h1 : maskedMean M (fun _ => (1 : ℝ)) ≤ uMean (fun _ : Clause × Ω => (1 : ℝ)) :=
        uMean_mono (fun p => by rw [mul_one]; exact bitR_le_one (M p))
      have h2 : uMean (fun _ : Clause × Ω => (1 : ℝ)) ≤ 1 := by
        unfold uMean; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact div_self_le_one _
      linarith
    calc _ ≤ Real.sqrt (maskedMean M fun p => e j p ^ 2) * Real.sqrt (maskedMean M fun _ => 1) := h
      _ ≤ Real.sqrt (24 * v₀) * 1 := by
          apply mul_le_mul (Real.sqrt_le_sqrt (hsq j)) _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_one]; exact hM1
      _ = _ := mul_one _
  have hprod : maskedMean M (fun p => |e 0 p * e 1 p|) ≤ 24 * v₀ := by
    calc _ ≤ Real.sqrt (maskedMean M fun p => e 0 p ^ 2) * Real.sqrt (maskedMean M fun p => e 1 p ^ 2) :=
          maskedMean_abs_mul_le M (e 0) (e 1)
      _ ≤ Real.sqrt (24 * v₀) * Real.sqrt (24 * v₀) :=
          mul_le_mul (Real.sqrt_le_sqrt (hsq 0)) (Real.sqrt_le_sqrt (hsq 1)) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = 24 * v₀ := Real.mul_self_sqrt (by positivity)
  -- (3) pointwise bound and assembly
  have hpt : ∀ p : Clause × Ω, |bitR (M p) *
      (clauseValue (neg p.1 0) (neg p.1 1) (S p.1 0 p.2) (S p.1 1 p.2) -
       clauseValue (neg p.1 0) (neg p.1 1)
         (bitAsReal (validityRound (con p.1 0 p.2) (S p.1 0 p.2)))
         (bitAsReal (validityRound (con p.1 1 p.2) (S p.1 1 p.2))))| ≤
      bitR (M p) * |e 0 p| + bitR (M p) * |e 1 p| + bitR (M p) * |e 0 p * e 1 p| := by
    intro p
    rw [abs_mul, abs_of_nonneg (bitR_nonneg _), abs_mul, ← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (clauseValue_sub_le _ _ _ _ _ _ (bitAsReal_mem _) (bitAsReal_mem _))
      (bitR_nonneg _)
  calc _ ≤ uMean (fun p : Clause × Ω => |bitR (M p) *
        (clauseValue (neg p.1 0) (neg p.1 1) (S p.1 0 p.2) (S p.1 1 p.2) -
         clauseValue (neg p.1 0) (neg p.1 1)
           (bitAsReal (validityRound (con p.1 0 p.2) (S p.1 0 p.2)))
           (bitAsReal (validityRound (con p.1 1 p.2) (S p.1 1 p.2))))|) := by
        unfold uMean
        rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card (Clause × Ω) : ℝ) from Nat.cast_nonneg _)]
        exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ uMean (fun p => bitR (M p) * |e 0 p| + bitR (M p) * |e 1 p| + bitR (M p) * |e 0 p * e 1 p|) :=
        uMean_mono hpt
    _ = maskedMean M (fun p => |e 0 p|) + maskedMean M (fun p => |e 1 p|) +
          maskedMean M (fun p => |e 0 p * e 1 p|) := by
        unfold maskedMean; rw [uMean_add, uMean_add]
    _ ≤ Real.sqrt (24 * v₀) + Real.sqrt (24 * v₀) + 24 * v₀ := by
        linarith [hone 0, hone 1, hprod]
    _ = 2 * Real.sqrt (24 * v₀) + 24 * v₀ := by ring

theorem maskedRounding_holds : MaskedRounding := by
  intro Clause Ω _ _ S con neg G v₀ hv hv24 hV _
  have h := maskedRounding_sharp S con neg G v₀ hv hV
  have hs : 24 * v₀ ≤ Real.sqrt (24 * v₀) := by
    have ht := Real.sq_sqrt (show (0 : ℝ) ≤ 24 * v₀ by positivity)
    have h1 : Real.sqrt (24 * v₀) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
    nlinarith [Real.sqrt_nonneg (24 * v₀)]
  have hs0 := Real.sqrt_nonneg (24 * v₀)
  linarith

end NearCubicWires.WireExponent3_5.Shared

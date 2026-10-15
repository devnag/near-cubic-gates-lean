import Proof.Wire_3_5.ValidityBridge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Shared
open Finset

/-! ## Independent draws from a finite weighted distribution -/

/-- The mean of `F` over `s` independent draws from the weights `w` (the product weight `∏_a w(f a)`). -/
noncomputable def drawMean {β : Type} [Fintype β] (w : β → ℝ) (s : ℕ) (F : (Fin s → β) → ℝ) : ℝ :=
  ∑ f : Fin s → β, (∏ a, w (f a)) * F f

/-- The sum `Σ_a Y(f a)` of one draw. -/
def drawSum {β : Type} (Y : β → ℝ) {s : ℕ} (f : Fin s → β) : ℝ := ∑ a, Y (f a)

theorem drawSum_cons {β : Type} (Y : β → ℝ) {s : ℕ} (b : β) (g : Fin s → β) :
    drawSum Y (Fin.cons b g : Fin (s + 1) → β) = Y b + drawSum Y g := by
  simp [drawSum, Fin.sum_univ_succ]

/-- One more draw: the product weight factors as the first draw times the rest. -/
theorem drawMean_succ {β : Type} [Fintype β] (w : β → ℝ) (s : ℕ) (F : (Fin (s + 1) → β) → ℝ) :
    drawMean w (s + 1) F = ∑ b, w b * drawMean w s (fun g => F (Fin.cons b g)) := by
  unfold drawMean
  rw [← (Fin.consEquiv (fun _ => β)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hc : (Fin.consEquiv (fun _ => β)) (b, g) = Fin.cons b g := rfl
  rw [hc, Fin.prod_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  ring

/-- The product weights have total mass one when `w` does. -/
theorem drawMean_weights_one {β : Type} [Fintype β] (w : β → ℝ) (hw : ∑ b, w b = 1) (s : ℕ) :
    ∑ f : Fin s → β, ∏ a, w (f a) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : Fin s) b => w b)]
  simp [hw]

theorem drawMean_weights_nonneg {β : Type} [Fintype β] (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) {s : ℕ}
    (f : Fin s → β) : 0 ≤ ∏ a, w (f a) :=
  Finset.prod_nonneg fun a _ => hw (f a)

/-- Linearity of `drawMean` on a polynomial of degree four in one statistic. -/
theorem drawMean_poly4 {β : Type} [Fintype β] (w : β → ℝ) (hw : ∑ b, w b = 1) (s : ℕ)
    (F : (Fin s → β) → ℝ) (c0 c1 c2 c3 c4 : ℝ) :
    drawMean w s (fun g => c0 + c1 * F g + c2 * F g ^ 2 + c3 * F g ^ 3 + c4 * F g ^ 4) =
      c0 + c1 * drawMean w s F + c2 * drawMean w s (fun g => F g ^ 2) +
        c3 * drawMean w s (fun g => F g ^ 3) + c4 * drawMean w s (fun g => F g ^ 4) := by
  unfold drawMean
  have h0 : ∑ f : Fin s → β, (∏ a, w (f a)) * c0 = c0 := by
    rw [← Finset.sum_mul, drawMean_weights_one w hw, one_mul]
  have hk : ∀ (c : ℝ) (G : (Fin s → β) → ℝ),
      ∑ f : Fin s → β, (∏ a, w (f a)) * (c * G f) = c * ∑ f : Fin s → β, (∏ a, w (f a)) * G f := by
    intro c G
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [mul_add, Finset.sum_add_distrib, h0, hk]

/-- Weighted sums of a degree-four polynomial in one variable. -/
theorem wsum_poly4 {β : Type} [Fintype β] (w Y : β → ℝ) (A B C D : ℝ) :
    ∑ b, w b * (Y b ^ 4 + A * Y b ^ 3 + B * Y b ^ 2 + C * Y b + D) =
      ∑ b, w b * Y b ^ 4 + A * ∑ b, w b * Y b ^ 3 + B * ∑ b, w b * Y b ^ 2 + C * ∑ b, w b * Y b +
        D * ∑ b, w b := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem drawMean_moments {β : Type} [Fintype β] (w Y : β → ℝ) (hw : ∑ b, w b = 1)
    (hY : ∑ b, w b * Y b = 0) (s : ℕ) :
    drawMean w s (fun f => drawSum Y f) = 0 ∧
      drawMean w s (fun f => drawSum Y f ^ 2) = (s : ℝ) * ∑ b, w b * Y b ^ 2 ∧
      drawMean w s (fun f => drawSum Y f ^ 4) =
        (s : ℝ) * ∑ b, w b * Y b ^ 4 + 3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2 := by
  induction s with
  | zero => simp [drawMean, drawSum]
  | succ s ih =>
    obtain ⟨ih1, ih2, ih4⟩ := ih
    set M1 := drawMean w s (fun f => drawSum Y f)
    set M2 := drawMean w s (fun f => drawSum Y f ^ 2)
    set M3 := drawMean w s (fun f => drawSum Y f ^ 3)
    set M4 := drawMean w s (fun f => drawSum Y f ^ 4)
    have e1 : ∀ y : ℝ, drawMean w s (fun g => y + drawSum Y g) = y + M1 := by
      intro y
      have h := drawMean_poly4 w hw s (fun g => drawSum Y g) y 1 0 0 0
      simp only [one_mul, zero_mul, add_zero] at h
      rw [h]
    have e2 : ∀ y : ℝ, drawMean w s (fun g => (y + drawSum Y g) ^ 2) = y ^ 2 + 2 * y * M1 + M2 := by
      intro y
      have h := drawMean_poly4 w hw s (fun g => drawSum Y g) (y ^ 2) (2 * y) 1 0 0
      simp only [one_mul, zero_mul, add_zero] at h
      rw [← h]
      unfold drawMean
      exact Finset.sum_congr rfl fun g _ => by ring
    have e4 : ∀ y : ℝ, drawMean w s (fun g => (y + drawSum Y g) ^ 4) =
        y ^ 4 + 4 * y ^ 3 * M1 + 6 * y ^ 2 * M2 + 4 * y * M3 + M4 := by
      intro y
      have h := drawMean_poly4 w hw s (fun g => drawSum Y g) (y ^ 4) (4 * y ^ 3) (6 * y ^ 2) (4 * y) 1
      simp only [one_mul] at h
      rw [← h]
      unfold drawMean
      exact Finset.sum_congr rfl fun g _ => by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [drawMean_succ]
      simp only [drawSum_cons, e1, ih1, add_zero]
      exact hY
    · rw [drawMean_succ]
      simp only [drawSum_cons, e2, ih1, ih2]
      have h := wsum_poly4 w Y 0 1 0 ((s : ℝ) * ∑ b, w b * Y b ^ 2)
      have hl : ∑ b, w b * (Y b ^ 2 + 2 * Y b * 0 + (s : ℝ) * ∑ b, w b * Y b ^ 2) =
          ∑ b, w b * (Y b ^ 4 * 0 + 0 * Y b ^ 3 + 1 * Y b ^ 2 + 0 * Y b + (s : ℝ) * ∑ b, w b * Y b ^ 2) :=
        Finset.sum_congr rfl fun b _ => by ring
      have h' : ∑ b, w b * (Y b ^ 4 * 0 + 0 * Y b ^ 3 + 1 * Y b ^ 2 + 0 * Y b + (s : ℝ) * ∑ b, w b * Y b ^ 2) =
          ∑ b, w b * Y b ^ 2 + (s : ℝ) * ∑ b, w b * Y b ^ 2 := by
        rw [show (fun b => w b * (Y b ^ 4 * 0 + 0 * Y b ^ 3 + 1 * Y b ^ 2 + 0 * Y b +
            (s : ℝ) * ∑ b, w b * Y b ^ 2)) = fun b => w b * (Y b ^ 2) + w b * ((s : ℝ) * ∑ b, w b * Y b ^ 2) by
          funext b; ring]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
      rw [hl, h']
      push_cast
      ring
    · rw [drawMean_succ]
      simp only [drawSum_cons, e4, ih1, ih2, ih4]
      have h := wsum_poly4 w Y 0 (6 * ((s : ℝ) * ∑ b, w b * Y b ^ 2)) (4 * M3)
        ((s : ℝ) * ∑ b, w b * Y b ^ 4 + 3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2)
      have hl : ∑ b, w b * (Y b ^ 4 + 4 * Y b ^ 3 * 0 + 6 * Y b ^ 2 * ((s : ℝ) * ∑ b, w b * Y b ^ 2) +
            4 * Y b * M3 + ((s : ℝ) * ∑ b, w b * Y b ^ 4 +
              3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2)) =
          ∑ b, w b * (Y b ^ 4 + 0 * Y b ^ 3 + 6 * ((s : ℝ) * ∑ b, w b * Y b ^ 2) * Y b ^ 2 +
            4 * M3 * Y b + ((s : ℝ) * ∑ b, w b * Y b ^ 4 +
              3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2)) :=
        Finset.sum_congr rfl fun b _ => by ring
      rw [hl, h, hY, hw]
      push_cast
      ring

theorem exists_le_of_weighted {ι : Type} [Fintype ι] [Nonempty ι] (W g : ι → ℝ) (hW : ∀ i, 0 ≤ W i)
    (hsum : ∑ i, W i = 1) (c : ℝ) (h : ∑ i, W i * g i ≤ c) : ∃ i, g i ≤ c := by
  obtain ⟨i0, -, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  refine ⟨i0, ?_⟩
  calc g i0 = ∑ i, W i * g i0 := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, W i * g i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmin i (Finset.mem_univ _)) (hW i)
    _ ≤ c := h

/-! ## The sampling distribution of `tr:sparse` -/

/-- The grid sign of a coefficient: `sgn(α) ∈ {−1,0,1}`. -/
noncomputable def gridSign (a : ℝ) : ℤ := if 0 < a then 1 else if a < 0 then -1 else 0

theorem gridSign_mul_abs (a : ℝ) : (gridSign a : ℝ) * |a| = a := by
  unfold gridSign
  split_ifs with h1 h2
  · simp [abs_of_pos h1]
  · simp [abs_of_neg h2]
  · have : a = 0 := by linarith [not_lt.mp h1, not_lt.mp h2]
    simp [this]

theorem gridSign_mem (a : ℝ) : gridSign a ∈ ({-1, 0, 1} : Finset ℤ) := by
  unfold gridSign; split_ifs <;> simp

theorem gridSign_sq_le (a : ℝ) : ((gridSign a : ℝ)) ^ 2 ≤ 1 := by
  unfold gridSign; split_ifs <;> norm_num

noncomputable def sparseWeight {J : Type} [Fintype J] (α : J → ℝ) (Λbar : ℝ) : Option J → ℝ
  | some j => |α j| / Λbar
  | none => 1 - (∑ j, |α j|) / Λbar

/-- The sign attached to a draw (zero for the zero atom). -/
noncomputable def sparseSign {J : Type} (α : J → ℝ) : Option J → ℤ
  | some j => gridSign (α j)
  | none => 0

/-- The atom value of a draw: `C_j(x)`, or `0` for the zero atom. -/
noncomputable def atomValue {J Ω : Type} (C : J → Ω → Bool) : Option J → Ω → ℝ
  | some j, x => bitR (C j x)
  | none, _ => 0

/-- The drawn value `R(x) = Λ̄·σ·C(x)`. -/
noncomputable def drawValue {J Ω : Type} (C : J → Ω → Bool) (α : J → ℝ) (Λbar : ℝ) (b : Option J) (x : Ω) : ℝ :=
  Λbar * (sparseSign α b : ℝ) * atomValue C b x

section Draw
variable {J Ω : Type} [Fintype J] (C : J → Ω → Bool) (α : J → ℝ) (Λbar : ℝ)

theorem sparseWeight_sum (hΛ : 0 < Λbar) : ∑ b, sparseWeight α Λbar b = 1 := by
  rw [Fintype.sum_option]
  simp only [sparseWeight]
  rw [← Finset.sum_div]
  have : Λbar ≠ 0 := hΛ.ne'
  ring

theorem sparseWeight_nonneg (hΛ : 0 < Λbar) (hmass : ∑ j, |α j| ≤ Λbar) (b : Option J) :
    0 ≤ sparseWeight α Λbar b := by
  cases b with
  | none =>
    simp only [sparseWeight, sub_nonneg]
    exact (div_le_one hΛ).mpr hmass
  | some j => exact div_nonneg (abs_nonneg _) hΛ.le

omit [Fintype J] in
theorem atomValue_mem (b : Option J) (x : Ω) : 0 ≤ atomValue C b x ∧ atomValue C b x ≤ 1 := by
  cases b with
  | none => simp [atomValue]
  | some j => exact ⟨bitR_nonneg _, bitR_le_one _⟩

theorem drawValue_mean (hΛ : 0 < Λbar) (x : Ω) :
    ∑ b, sparseWeight α Λbar b * drawValue C α Λbar b x = ∑ j, α j * bitR (C j x) := by
  rw [Fintype.sum_option]
  simp only [sparseWeight, drawValue, sparseSign, atomValue, Int.cast_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL : Λbar / Λbar = 1 := div_self hΛ.ne'
  calc |α j| / Λbar * (Λbar * (gridSign (α j) : ℝ) * bitR (C j x))
      = (Λbar / Λbar) * (((gridSign (α j) : ℝ) * |α j|) * bitR (C j x)) := by ring
    _ = α j * bitR (C j x) := by rw [hL, one_mul, gridSign_mul_abs]

/-- `|T(x)| ≤ Λ̄`. -/
theorem correlator_abs_le (hmass : ∑ j, |α j| ≤ Λbar) (x : Ω) : |∑ j, α j * bitR (C j x)| ≤ Λbar := by
  calc |∑ j, α j * bitR (C j x)| ≤ ∑ j, |α j * bitR (C j x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |α j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (bitR_nonneg _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (bitR_le_one _)
    _ ≤ Λbar := hmass

omit [Fintype J] in
/-- `|R(x)| ≤ Λ̄`. -/
theorem drawValue_abs_le (hΛ : 0 < Λbar) (b : Option J) (x : Ω) : |drawValue C α Λbar b x| ≤ Λbar := by
  unfold drawValue
  have hσ : |(sparseSign α b : ℝ)| ≤ 1 := by
    cases b with
    | none => simp [sparseSign]
    | some j =>
      have := gridSign_sq_le (α j)
      simp only [sparseSign]
      rw [← sq_le_one_iff_abs_le_one]; exact this
  have ha := atomValue_mem C b x
  rw [abs_mul, abs_mul, abs_of_pos hΛ, abs_of_nonneg ha.1]
  calc Λbar * |(sparseSign α b : ℝ)| * atomValue C b x ≤ Λbar * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hσ hΛ.le) ha.2 ha.1 (by positivity)
    _ = Λbar := by ring

/-- The second moment of a draw: `E R(x)² ≤ Λ̄·Σ|α_j| ≤ Λ̄²`. -/
theorem drawValue_sq_mean_le (hΛ : 0 < Λbar) (hmass : ∑ j, |α j| ≤ Λbar) (x : Ω) :
    ∑ b, sparseWeight α Λbar b * drawValue C α Λbar b x ^ 2 ≤ Λbar ^ 2 := by
  rw [Fintype.sum_option]
  simp only [sparseWeight, drawValue, sparseSign, atomValue, Int.cast_zero, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  calc ∑ j, |α j| / Λbar * (Λbar * (gridSign (α j) : ℝ) * bitR (C j x)) ^ 2
      ≤ ∑ j, |α j| * Λbar := Finset.sum_le_sum fun j _ => by
        have hs := gridSign_sq_le (α j)
        have hb0 := bitR_nonneg (C j x)
        have hb1 := bitR_le_one (C j x)
        have hb : bitR (C j x) ^ 2 ≤ 1 := by nlinarith
        have hsb : (gridSign (α j) : ℝ) ^ 2 * bitR (C j x) ^ 2 ≤ 1 := by
          calc (gridSign (α j) : ℝ) ^ 2 * bitR (C j x) ^ 2 ≤ 1 * 1 :=
                mul_le_mul hs hb (sq_nonneg _) zero_le_one
            _ = 1 := by ring
        have e : |α j| / Λbar * (Λbar * (gridSign (α j) : ℝ) * bitR (C j x)) ^ 2 =
            (|α j| * Λbar) * ((gridSign (α j) : ℝ) ^ 2 * bitR (C j x) ^ 2) := by
          field_simp
        rw [e]
        exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hΛ.le) hsb
    _ = (∑ j, |α j|) * Λbar := by rw [Finset.sum_mul]
    _ ≤ Λbar * Λbar := mul_le_mul_of_nonneg_right hmass hΛ.le
    _ = Λbar ^ 2 := by ring

end Draw

/-! ## The per-input fourth moment and the witness -/

theorem sparse_arith (s : ℝ) (hs : 1 ≤ s) : (16 * s + 3 * (s * (s - 1))) / s ^ 4 ≤ 19 / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : 16 * s + 3 * (s * (s - 1)) ≤ 19 * s ^ 2 := by nlinarith
  calc (16 * s + 3 * (s * (s - 1))) * s ^ 2 ≤ 19 * s ^ 2 * s ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 19 * s ^ 4 := by ring

theorem sparse_arith_sixteen (s : ℝ) (hs : 1 ≤ s) : (16 * s + 3 * (s * (s - 1))) / s ^ 4 ≤ 16 / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : 16 * s + 3 * (s * (s - 1)) ≤ 16 * s ^ 2 := by nlinarith
  calc (16 * s + 3 * (s * (s - 1))) * s ^ 2 ≤ 16 * s ^ 2 * s ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 16 * s ^ 4 := by ring

section Witness
variable {J Ω : Type} [Fintype J] (C : J → Ω → Bool) (α : J → ℝ) (Λbar : ℝ) (s : ℕ)

/-- The witness of one draw `f : Fin s → Option J`, as displayed in `SparseWitness`: `(Λ̄/s)Σ_a σ_a C_{j_a}(x)`. -/
noncomputable def sparseOf (f : Fin s → Option J) (x : Ω) : ℝ :=
  Λbar / s * ∑ a, (sparseSign α (f a) : ℝ) * atomValue C (f a) x

theorem sparse_fourth_moment (hs : 1 ≤ s) (hΛ : 1 ≤ Λbar) (hmass : ∑ j, |α j| ≤ Λbar) (x : Ω) :
    drawMean (sparseWeight α Λbar) s
        (fun f => (sparseOf C α Λbar s f x - ∑ j, α j * bitR (C j x)) ^ 4) ≤
      19 * Λbar ^ 4 / (s : ℝ) ^ 2 := by
  have hΛ0 : 0 < Λbar := by linarith
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ j, α j * bitR (C j x) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : Option J → ℝ, w = sparseWeight α Λbar := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Option J → ℝ, Y = fun b => drawValue C α Λbar b x - T := ⟨_, rfl⟩
  rw [← hT, ← hwdef]
  have hw : ∑ b, w b = 1 := hwdef ▸ sparseWeight_sum α Λbar hΛ0
  have hwn : ∀ b, 0 ≤ w b := hwdef ▸ sparseWeight_nonneg α Λbar hΛ0 hmass
  have hmean : ∑ b, w b * drawValue C α Λbar b x = T := hwdef ▸ hT ▸ drawValue_mean C α Λbar hΛ0 x
  have hY : ∑ b, w b * Y b = 0 := by
    have : ∑ b, w b * Y b = ∑ b, w b * drawValue C α Λbar b x - T * ∑ b, w b := by
      simp only [hYdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, hw, hmean]; ring
  -- the error of a draw is `s⁻¹ Σ_a Y(f a)`
  have herr : ∀ f : Fin s → Option J, sparseOf C α Λbar s f x - T = (1 / (s : ℝ)) * drawSum Y f := by
    intro f
    have hd : drawSum Y f = Λbar * ∑ a, (sparseSign α (f a) : ℝ) * atomValue C (f a) x - s * T := by
      unfold drawSum
      simp only [hYdef, drawValue, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [hd]
    unfold sparseOf
    field_simp
  have hpow : ∀ f : Fin s → Option J, (sparseOf C α Λbar s f x - T) ^ 4 = (1 / (s : ℝ) ^ 4) * drawSum Y f ^ 4 := by
    intro f; rw [herr f]; ring
  obtain ⟨-, -, h4⟩ := drawMean_moments w Y hw hY s
  have hlin : drawMean w s (fun f => (sparseOf C α Λbar s f x - T) ^ 4) =
      (1 / (s : ℝ) ^ 4) * drawMean w s (fun f => drawSum Y f ^ 4) := by
    unfold drawMean
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    dsimp only
    rw [hpow f]; ring
  -- the moments of one centred draw
  have hm2 : ∑ b, w b * Y b ^ 2 ≤ Λbar ^ 2 := by
    have e : ∑ b, w b * Y b ^ 2 =
        ∑ b, w b * drawValue C α Λbar b x ^ 2 - 2 * T * ∑ b, w b * drawValue C α Λbar b x +
          T ^ 2 * ∑ b, w b := by
      simp only [hYdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, hw, hmean]
    have := hwdef ▸ drawValue_sq_mean_le C α Λbar hΛ0 hmass x
    nlinarith [sq_nonneg T]
  have hm2' : 0 ≤ ∑ b, w b * Y b ^ 2 := Finset.sum_nonneg fun b _ => mul_nonneg (hwn b) (sq_nonneg _)
  have hm4 : ∑ b, w b * Y b ^ 4 ≤ 16 * Λbar ^ 4 := by
    have hYb : ∀ b, Y b ^ 4 ≤ 16 * Λbar ^ 4 := by
      intro b
      have h1 := drawValue_abs_le C α Λbar hΛ0 b x
      have h2 : |T| ≤ Λbar := hT ▸ correlator_abs_le C α Λbar hmass x
      have h3 : |Y b| ≤ 2 * Λbar := by
        calc |Y b| = |drawValue C α Λbar b x - T| := by rw [hYdef]
          _ ≤ |drawValue C α Λbar b x| + |T| := abs_sub _ _
          _ ≤ 2 * Λbar := by linarith
      calc Y b ^ 4 = |Y b| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ (2 * Λbar) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h3 4
        _ = 16 * Λbar ^ 4 := by ring
    calc ∑ b, w b * Y b ^ 4 ≤ ∑ b, w b * (16 * Λbar ^ 4) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hYb b) (hwn b)
      _ = 16 * Λbar ^ 4 := by rw [← Finset.sum_mul, hw, one_mul]
  -- assembly
  rw [hlin, h4]
  have hss : 0 ≤ (s : ℝ) * ((s : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
  have hbound : (s : ℝ) * ∑ b, w b * Y b ^ 4 + 3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2 ≤
      (16 * (s : ℝ) + 3 * ((s : ℝ) * ((s : ℝ) - 1))) * Λbar ^ 4 := by
    have hsq : (∑ b, w b * Y b ^ 2) ^ 2 ≤ (Λbar ^ 2) ^ 2 := pow_le_pow_left₀ hm2' hm2 2
    have hA : (s : ℝ) * ∑ b, w b * Y b ^ 4 ≤ (s : ℝ) * (16 * Λbar ^ 4) :=
      mul_le_mul_of_nonneg_left hm4 (by linarith)
    have hB : 3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2 ≤
        3 * ((s : ℝ) * ((s : ℝ) - 1)) * (Λbar ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith [hA, hB]
  have harith := sparse_arith (s : ℝ) hsR
  have hs4 : (0 : ℝ) < (s : ℝ) ^ 4 := by positivity
  calc 1 / (s : ℝ) ^ 4 * ((s : ℝ) * ∑ b, w b * Y b ^ 4 +
        3 * ((s : ℝ) * ((s : ℝ) - 1)) * (∑ b, w b * Y b ^ 2) ^ 2)
      ≤ 1 / (s : ℝ) ^ 4 * ((16 * (s : ℝ) + 3 * ((s : ℝ) * ((s : ℝ) - 1))) * Λbar ^ 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (16 * (s : ℝ) + 3 * ((s : ℝ) * ((s : ℝ) - 1))) / (s : ℝ) ^ 4 * Λbar ^ 4 := by ring
    _ ≤ 19 / (s : ℝ) ^ 2 * Λbar ^ 4 := mul_le_mul_of_nonneg_right harith (by positivity)
    _ = 19 * Λbar ^ 4 / (s : ℝ) ^ 2 := by ring

end Witness

/-- `uMean` of a function bounded by a nonnegative constant. -/
theorem uMean_le_const {Ω : Type} [Fintype Ω] (g : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ x, g x ≤ c) :
    uMean g ≤ c := by
  unfold uMean
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; exact hc
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    calc ∑ x, g x ≤ ∑ _x : Ω, c := Finset.sum_le_sum fun x _ => hg x
      _ = c * Fintype.card Ω := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

theorem sparseWitness_holds : SparseWitness := by
  intro J Ω _ _ C α Λbar s hs hΛ hmass
  classical
  have hΛ0 : 0 < Λbar := by linarith
  set w := sparseWeight α Λbar
  -- the weighted average over draws of the `L₄` error
  have havg : ∑ f : Fin s → Option J, (∏ a, w (f a)) *
      uMean (fun x => (sparseOf C α Λbar s f x - ∑ j, α j * bitR (C j x)) ^ 4) ≤
        19 * Λbar ^ 4 / (s : ℝ) ^ 2 := by
    have hswap : ∑ f : Fin s → Option J, (∏ a, w (f a)) *
        uMean (fun x => (sparseOf C α Λbar s f x - ∑ j, α j * bitR (C j x)) ^ 4) =
        uMean (fun x => drawMean w s
          (fun f => (sparseOf C α Λbar s f x - ∑ j, α j * bitR (C j x)) ^ 4)) := by
      unfold uMean drawMean
      simp only [mul_div_assoc', Finset.mul_sum, ← Finset.sum_div]
      rw [Finset.sum_comm]
    rw [hswap]
    exact uMean_le_const _ _ (by positivity) fun x => sparse_fourth_moment C α Λbar s hs hΛ hmass x
  obtain ⟨f, hf⟩ := exists_le_of_weighted (fun f : Fin s → Option J => ∏ a, w (f a)) _
    (drawMean_weights_nonneg w (sparseWeight_nonneg α Λbar hΛ0 hmass))
    (drawMean_weights_one w (sparseWeight_sum α Λbar hΛ0) s) _ havg
  refine ⟨fun a => sparseSign α (f a), f, fun a => ?_, ?_⟩
  · show sparseSign α (f a) ∈ _
    rcases f a with _ | j
    · simp [sparseSign]
    · exact gridSign_mem (α j)
  · refine Eq.trans_le ?_ hf
    congr 1
    funext x
    congr 2
    unfold sparseOf
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    rcases f a with _ | j <;> rfl

theorem sparseWitness_delta {J Ω : Type} [Fintype J] [Fintype Ω] (C : J → Ω → Bool) (α : J → ℝ) (Λbar : ℝ)
    (s : ℕ) (hs : 1 ≤ s) (hΛ : 1 ≤ Λbar) (hmass : ∑ j, |α j| ≤ Λbar) (δ : ℝ)
    (hsδ : 19 * Λbar ^ 4 ≤ (s : ℝ) ^ 2 * δ ^ 4) :
    ∃ (σ : Fin s → ℤ) (atom : Fin s → Option J), (∀ a, σ a ∈ ({-1, 0, 1} : Finset ℤ)) ∧
      Λbar / s * ∑ a, |(σ a : ℝ)| ≤ Λbar ∧
      uMean (fun x : Ω =>
        (Λbar / s * ∑ a, (σ a : ℝ) * (match atom a with | some j => bitR (C j x) | none => 0) -
          ∑ j, α j * bitR (C j x)) ^ 4) ≤ δ ^ 4 := by
  obtain ⟨σ, atom, hσ, hbound⟩ := sparseWitness_holds C α Λbar s hs hΛ hmass
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  refine ⟨σ, atom, hσ, ?_, ?_⟩
  · have habs : ∀ a, |(σ a : ℝ)| ≤ 1 := by
      intro a
      have h := hσ a
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h <;> simp [h]
    calc Λbar / s * ∑ a, |(σ a : ℝ)| ≤ Λbar / s * ∑ _a : Fin s, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => habs a) (by positivity)
      _ = Λbar := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          field_simp
  · refine hbound.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith

/-! ## Executable twin (test before prove) and non-vacuity -/

/-- Exact integer twin of the sparse witness's `L₄` error on a tiny instance (test before prove). Coefficients are
`α_j = a_j/d` and `Λ̄ = Λ/d`; atoms are truth-table rows over `P` points; a draw lists `s` atom choices (`none` is
the zero atom), each with the grid sign of its coefficient. At each point `s·d·(S−T)(x) = Λ·Σ_a σ_a C_{j_a}(x) −
s·Σ_j a_j C_j(x)`, so `mean_x (S−T)⁴ ≤ 19Λ̄⁴/s²` iff `Σ_x (s·d·(S−T)(x))⁴ ≤ 19·Λ⁴·s²·P`. -/
def sparseErrorNumRef (atoms : List (List Bool)) (a : List ℤ) (Λ : ℤ) (draw : List (Option ℕ)) : ℤ :=
  let points := (atoms.headD []).length
  let s : ℤ := draw.length
  let bit : ℕ → ℕ → ℤ := fun j x => if (atoms.getD j []).getD x false then 1 else 0
  let val : Option ℕ → ℕ → ℤ := fun o x => match o with
    | some j => Int.sign (a.getD j 0) * bit j x
    | none => 0
  let E : ℕ → ℤ := fun x =>
    Λ * (draw.map fun o => val o x).sum - s * ((List.range atoms.length).map fun j => a.getD j 0 * bit j x).sum
  ((List.range points).map fun x => E x ^ 4).sum

/-- All draws of length `s` over `m` atoms. -/
def allDraws (m : ℕ) : ℕ → List (List (Option ℕ))
  | 0 => [[]]
  | s + 1 => (allDraws m s).flatMap fun d => (none :: (List.range m).map some).map fun o => o :: d

/-- The best draw's scaled error, by enumeration. -/
def bestSparseErrorNumRef (atoms : List (List Bool)) (a : List ℤ) (Λ : ℤ) (s : ℕ) : ℤ :=
  ((allDraws atoms.length s).map (sparseErrorNumRef atoms a Λ)).foldl min (sparseErrorNumRef atoms a Λ [])

/-- Tiny instance: two atoms on four points, `α = (1/2, −1/3)` (`a = (3,−2)`, `d = 6`), `Λ̄ = 1` (`Λ = 6`), `s = 2`:
the best draw meets the lemma's bound `19Λ̄⁴/s²`. -/
example : bestSparseErrorNumRef [[true, false, true, false], [true, true, false, false]] [3, -2] 6 2 ≤
    19 * 6 ^ 4 * 2 ^ 2 * 4 := by
  decide

/-- The same instance at `s = 3`. -/
example : bestSparseErrorNumRef [[true, false, true, false], [true, true, false, false]] [3, -2] 6 3 ≤
    19 * 6 ^ 4 * 3 ^ 2 * 4 := by
  decide

/-- The conclusion has teeth: the zero witness (every draw the zero atom) violates the bound for `T = C` with one
always-true atom, `Λ̄ = 1`, `s = 5` (`‖0 − 1‖₄⁴ = 1 > 19/25`). A witness must approximate `T`. -/
theorem sparseWitness_zero_fails :
    ¬ uMean (fun x : Fin 1 => (sparseOf (fun (_ : Fin 1) (_ : Fin 1) => true) (fun _ => (1 : ℝ)) 1 5
        (fun _ => none) x - ∑ j : Fin 1, (fun _ => (1 : ℝ)) j * bitR ((fun (_ : Fin 1) (_ : Fin 1) => true) j x)) ^ 4)
      ≤ 19 * 1 ^ 4 / (5 : ℝ) ^ 2 := by
  simp [sparseOf, sparseSign, atomValue, uMean, bitR]
  norm_num

/-- Non-vacuity: the hypotheses of `SparseWitness` are satisfiable (one atom, `α = 1/2`, `Λ̄ = 1`, `s = 1`), and the
conclusion then bounds a genuine approximation of `T = C/2`. -/
theorem sparseWitness_hypotheses_sat :
    ∃ (C : Fin 1 → Fin 2 → Bool) (α : Fin 1 → ℝ) (Λbar : ℝ) (s : ℕ),
      1 ≤ s ∧ 1 ≤ Λbar ∧ ∑ j, |α j| ≤ Λbar ∧ (∃ x, ∑ j, α j * bitR (C j x) ≠ 0) :=
  ⟨fun _ x => decide (x = 0), fun _ => 1 / 2, 1, 1, le_rfl, le_rfl, by norm_num,
    ⟨0, by simp [bitR]⟩⟩

end NearCubicWires.WireExponent3_5.Transfer

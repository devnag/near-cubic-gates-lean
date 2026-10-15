import Proof.Wire_3_5.FilterMajorant
import Proof.Wire_3_5.MaskedExpectation

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.SupplierPipeline Finset

/-! ## The greedy method of conditional expectations on a binary seed (S3.6) -/

/-- The greedy seed: fix the bits one at a time, each time taking the child whose mean is no larger. -/
noncomputable def greedy : (m : ℕ) → ((Fin m → Bool) → ℝ) → (Fin m → Bool)
  | 0, _ => Fin.elim0
  | m + 1, Φ =>
    let Φf : (Fin m → Bool) → ℝ := fun s => Φ (Fin.cons false s)
    let Φt : (Fin m → Bool) → ℝ := fun s => Φ (Fin.cons true s)
    if uMean Φf ≤ uMean Φt then Fin.cons false (greedy m Φf) else Fin.cons true (greedy m Φt)

theorem uMean_cons (m : ℕ) (Φ : (Fin (m + 1) → Bool) → ℝ) :
    uMean Φ = (uMean (fun s => Φ (Fin.cons false s)) + uMean (fun s => Φ (Fin.cons true s))) / 2 := by
  unfold uMean
  have hsum : ∑ s, Φ s = ∑ s : Fin m → Bool, Φ (Fin.cons false s) + ∑ s : Fin m → Bool, Φ (Fin.cons true s) := by
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]; rfl
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  rw [pow_succ]
  field_simp

theorem greedy_le_mean (m : ℕ) (Φ : (Fin m → Bool) → ℝ) : Φ (greedy m Φ) ≤ uMean Φ := by
  induction m with
  | zero =>
    unfold uMean
    simp only [Fintype.card_unique, Nat.cast_one, div_one, Fintype.sum_unique]
    exact le_of_eq (congrArg Φ (Subsingleton.elim _ _))
  | succ m ih =>
    rw [uMean_cons]
    simp only [greedy]
    split_ifs with h
    · have := ih (fun s => Φ (Fin.cons false s)); linarith
    · have := ih (fun s => Φ (Fin.cons true s)); push Not at h; linarith

/-- The draft statement `GreedySeedFixing` (S3.6), proved. -/
theorem greedySeedFixing : GreedySeedFixing := fun m Φ => ⟨greedy m Φ, greedy_le_mean m Φ⟩

/-! ## The abstract soft-mask lemma -/

section Soft
variable {X Hs Ea : Type} [Fintype X] [Fintype Hs] [Fintype Ea] [Nonempty X] [Nonempty Hs] [Nonempty Ea]

noncomputable def auxMean (Faux : Ea → X → Bool) (x : X) : ℝ := uMean fun e => bitR (Faux e x)

noncomputable def softObjective (Faux : Ea → X → Bool) (H : Hs → X → ℝ) (h : Hs) : ℝ :=
  uMean fun x => auxMean Faux x * H h x

theorem uMean_nonneg {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ uMean f :=
  div_nonneg (Finset.sum_nonneg fun ω _ => hf ω) (Nat.cast_nonneg _)

theorem uMean_le_of_le {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) (c : ℝ) (hf : ∀ ω, f ω ≤ c) : uMean f ≤ c := by
  unfold uMean
  rw [div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
  calc ∑ ω, f ω ≤ ∑ _ω : Ω, c := Finset.sum_le_sum fun ω _ => hf ω
    _ = c * Fintype.card Ω := by simp [mul_comm]

omit [Fintype X] [Nonempty X] [Nonempty Ea] in
theorem auxMean_nonneg (Faux : Ea → X → Bool) (x : X) : 0 ≤ auxMean Faux x :=
  uMean_nonneg _ fun _ => bitR_nonneg _

omit [Fintype X] [Nonempty X] in
theorem auxMean_le_one (Faux : Ea → X → Bool) (x : X) : auxMean Faux x ≤ 1 :=
  uMean_le_of_le _ 1 fun _ => bitR_le_one _

omit [Nonempty X] [Nonempty Hs] in
theorem uMean_swap (f : Hs → X → ℝ) : uMean (fun h => uMean fun x => f h x) = uMean fun x => uMean fun h => f h x := by
  unfold uMean
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm, div_div, div_div, mul_comm]

theorem mean_softObjective_le (Faux : Ea → X → Bool) (H : Hs → X → ℝ) (w : X → ℕ) (cap2 : ℕ) (ξ εaux Hmax : ℝ)
    (hξ : 0 ≤ ξ) (hε : 0 ≤ εaux) (hH0 : ∀ h x, 0 ≤ H h x) (hHmax : ∀ h x, H h x ≤ Hmax)
    (hlow : ∀ x, w x ≤ cap2 → uMean (fun h => H h x) ≤ ξ)
    (hhigh : ∀ x, cap2 < w x → auxMean Faux x ≤ εaux) :
    uMean (fun h => softObjective Faux H h) ≤ ξ + εaux * Hmax := by
  unfold softObjective
  rw [uMean_swap (fun h x => auxMean Faux x * H h x)]
  have hHm : 0 ≤ Hmax := le_trans (hH0 (Classical.arbitrary Hs) (Classical.arbitrary X)) (hHmax _ _)
  apply uMean_le_of_le
  intro x
  have hfac : uMean (fun h => auxMean Faux x * H h x) = auxMean Faux x * uMean (fun h => H h x) := by
    unfold uMean; rw [← Finset.mul_sum, mul_div_assoc]
  rw [hfac]
  have hm0 : 0 ≤ uMean (fun h => H h x) := uMean_nonneg _ fun h => hH0 h x
  have hmmax : uMean (fun h => H h x) ≤ Hmax := uMean_le_of_le _ _ fun h => hHmax h x
  have ha0 := auxMean_nonneg Faux x
  have ha1 := auxMean_le_one Faux x
  by_cases hw : w x ≤ cap2
  · have := hlow x hw
    nlinarith [mul_nonneg hε hHm]
  · have := hhigh x (by omega)
    have hξ0 : auxMean Faux x * uMean (fun h => H h x) ≤ εaux * Hmax :=
      mul_le_mul this hmmax hm0 hε
    linarith

omit [Fintype Hs] [Nonempty X] [Nonempty Hs] [Nonempty Ea] in

theorem fixed_failure_le (Faux : Ea → X → Bool) (H : Hs → X → ℝ) (w : X → ℕ) (cap1 : ℕ) (εaux : ℝ)
    (hε1 : εaux < 1) (hH0 : ∀ h x, 0 ≤ H h x) (hcomp : ∀ x, w x ≤ cap1 → 1 - εaux ≤ auxMean Faux x)
    (h : Hs) (Err : X → Bool) (hdom : ∀ x, Err x = true → 1 ≤ H h x) :
    uMean (fun x => bitR (decide (w x ≤ cap1) && Err x)) ≤ softObjective Faux H h / (1 - εaux) := by
  have hpos : 0 < 1 - εaux := by linarith
  unfold softObjective
  rw [le_div_iff₀ hpos]
  have : uMean (fun x => bitR (decide (w x ≤ cap1) && Err x)) * (1 - εaux) =
      uMean fun x => bitR (decide (w x ≤ cap1) && Err x) * (1 - εaux) := by
    unfold uMean; simp only [div_mul_eq_mul_div, Finset.sum_mul]
  rw [this]
  apply uMean_mono
  intro x
  by_cases hw : w x ≤ cap1
  · cases hE : Err x
    · simp [bitR]; exact mul_nonneg (auxMean_nonneg _ _) (hH0 h x)
    · simp only [hw, decide_true, Bool.and_self, bitR, if_true, one_mul]
      have := hdom x hE; have := hcomp x hw
      nlinarith [auxMean_nonneg Faux x]
  · simp [bitR, hw]; exact mul_nonneg (auxMean_nonneg _ _) (hH0 h x)

theorem filt_soft (Faux : Ea → X → Bool) (H : Hs → X → ℝ) (w : X → ℕ) (cap1 cap2 : ℕ) (ξ εaux Hmax : ℝ)
    (hξ : 0 ≤ ξ) (hε : 0 ≤ εaux) (hε1 : εaux < 1) (hH0 : ∀ h x, 0 ≤ H h x) (hHmax : ∀ h x, H h x ≤ Hmax)
    (hlow : ∀ x, w x ≤ cap2 → uMean (fun h => H h x) ≤ ξ)
    (hhigh : ∀ x, cap2 < w x → auxMean Faux x ≤ εaux)
    (hcomp : ∀ x, w x ≤ cap1 → 1 - εaux ≤ auxMean Faux x)
    (Err : Hs → X → Bool) (hdom : ∀ h x, Err h x = true → 1 ≤ H h x)
    {m : ℕ} (code : (Fin m → Bool) ≃ Hs) :
    let hstar := code (greedy m fun s => softObjective Faux H (code s))
    uMean (fun x => bitR (decide (w x ≤ cap1) && Err hstar x)) ≤ (ξ + εaux * Hmax) / (1 - εaux) := by
  intro hstar
  have hpos : 0 < 1 - εaux := by linarith
  refine (fixed_failure_le Faux H w cap1 εaux hε1 hH0 hcomp hstar (Err hstar) (hdom hstar)).trans ?_
  apply div_le_div_of_nonneg_right _ hpos.le
  have hg := greedy_le_mean m fun s => softObjective Faux H (code s)
  have hmean : uMean (fun s => softObjective Faux H (code s)) = uMean (fun h => softObjective Faux H h) := by
    unfold uMean
    rw [Fintype.card_congr code]
    congr 1
    exact code.sum_comp (fun h => softObjective Faux H h)
  rw [hmean] at hg
  exact hg.trans (mean_softObjective_le Faux H w cap2 ξ εaux Hmax hξ hε hH0 hHmax hlow hhigh)

end Soft

section Observable
variable {X Er : Type} [Fintype X] [Fintype Er] [Nonempty X] [Nonempty Er]

theorem uMean_fst (f : X → ℝ) : uMean (fun p : X × Er => f p.1) = uMean f := by
  unfold uMean
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod]
  rw [← Finset.mul_sum]
  push_cast
  have : (0 : ℝ) < Fintype.card Er := Nat.cast_pos.mpr Fintype.card_pos
  field_simp

theorem observable_error_le (Freg : Er → X → Bool) (w : X → ℕ) (cap1 : ℕ) (ξreg δ : ℝ) (hξ0 : 0 ≤ ξreg)
    (hsound : ∀ x, cap1 < w x → uMean (fun e => bitR (Freg e x)) ≤ ξreg)
    (R Rhat Err : X → Bool) (hagree : ∀ x, w x ≤ cap1 → Err x = false → Rhat x = R x)
    (hδ : uMean (fun x => bitR (decide (w x ≤ cap1) && Err x)) ≤ δ) :
    uMean (fun p : X × Er => bitR (Freg p.2 p.1) * |bitR (Rhat p.1) - bitR (R p.1)|) ≤ δ + ξreg := by
  apply maskedRowError_holds (fun p : X × Er => Freg p.2 p.1) (fun p => Rhat p.1) (fun p => R p.1)
    (fun p => Err p.1) (fun p => decide (cap1 < w p.1)) δ ξreg
  · intro p hover hfail
    simp only [decide_eq_false_iff_not, not_lt] at hover
    exact hagree p.1 hover hfail
  · have : (fun p : X × Er => bitR (Err p.1 && !decide (cap1 < w p.1))) =
        fun p => bitR (decide (w p.1 ≤ cap1) && Err p.1) := by
      funext p; cases Err p.1 <;> by_cases h : cap1 < w p.1 <;> simp [h, bitR]
    rw [this, uMean_fst (fun x => bitR (decide (w x ≤ cap1) && Err x))]; exact hδ
  · -- the regular filter on the over-cap inputs
    have hsplit : uMean (fun p : X × Er => bitR (Freg p.2 p.1 && decide (cap1 < w p.1))) =
        uMean fun x => if cap1 < w x then uMean (fun e => bitR (Freg e x)) else 0 := by
      unfold uMean
      rw [Fintype.sum_prod_type, Fintype.card_prod]
      push_cast
      rw [mul_comm, ← div_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : cap1 < w x
      · simp [h]
      · simp [h, bitR]
    rw [hsplit]
    apply uMean_le_of_le
    intro x; split_ifs with h
    · exact hsound x h
    · exact hξ0

end Observable

end NearCubicWires.WireExponent3_5.Filters

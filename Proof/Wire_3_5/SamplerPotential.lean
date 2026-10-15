import Proof.Wire_3_5.SamplerTrace
import Proof.Wire_3_5.MaskedExpectation

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.Shared Finset Matrix

variable {N Q : ℕ}

/-- `tr((EEᵀ)⁴) = ‖(EEᵀ)²‖²_F ≥ 0`. -/
theorem trace_pow4_nonneg (E : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ Matrix.trace ((E * Eᵀ) ^ 4) := by
  set P := (E * Eᵀ) ^ 2 with hPdef
  have hP : Pᵀ = P := by rw [hPdef, Matrix.transpose_pow, Matrix.transpose_mul, Matrix.transpose_transpose]
  have h4 : (E * Eᵀ) ^ 4 = Pᵀ * P := by rw [hP, hPdef, ← pow_add]
  rw [h4]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

theorem dot_self_le_card (a : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) : a ⬝ᵥ a ≤ N := by
  simp only [dotProduct]
  calc ∑ i, a i * a i ≤ ∑ _i : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro i _
        have := ha i
        have h2 : a i * a i = |a i| ^ 2 := by rw [sq_abs, sq]
        rw [h2]; nlinarith [abs_nonneg (a i)]
    _ = N := by simp

/-- The real bilinear bound for selectors with coordinates in `[−1, 1]`: `(aᵀEb)⁸ ≤ N⁸·tr((EEᵀ)⁴)`. -/
theorem rbil_pow8_le (E : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) :
    (a ⬝ᵥ (E *ᵥ b)) ^ 8 ≤ (N : ℝ) ^ 8 * Matrix.trace ((E * Eᵀ) ^ 4) := by
  have h := bilinear_pow8_le E a b
  rw [trace_transpose_mul_pow] at h
  have hT := trace_pow4_nonneg E
  have haN := dot_self_le_card a ha
  have hbN := dot_self_le_card b hb
  have ha0 : 0 ≤ a ⬝ᵥ a := dot_self_nonneg' a
  have hb0 : 0 ≤ b ⬝ᵥ b := dot_self_nonneg' b
  calc (a ⬝ᵥ (E *ᵥ b)) ^ 8 ≤ (a ⬝ᵥ a) ^ 4 * (b ⬝ᵥ b) ^ 4 * Matrix.trace ((E * Eᵀ) ^ 4) := h
    _ ≤ (N : ℝ) ^ 4 * (N : ℝ) ^ 4 * Matrix.trace ((E * Eᵀ) ^ 4) := by
        apply mul_le_mul_of_nonneg_right _ hT
        exact mul_le_mul (pow_le_pow_left₀ ha0 haN 4) (pow_le_pow_left₀ hb0 hbN 4) (by positivity) (by positivity)
    _ = (N : ℝ) ^ 8 * Matrix.trace ((E * Eᵀ) ^ 4) := by ring

/-- The complex bilinear form `aᵀEb = Σ_{u,v} a_u b_v E(u,v)` of a real matrix. -/
noncomputable def cbil (E : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℂ) : ℂ := ∑ u, ∑ v, a u * b v * (E u v : ℂ)

/-- The real bilinear form as a double sum. -/
theorem dot_mulVec_eq (E : Matrix (Fin N) (Fin N) ℝ) (x y : Fin N → ℝ) :
    x ⬝ᵥ (E *ᵥ y) = ∑ u, ∑ v, x u * y v * E u v := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  ring

theorem cbil_re (E : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℂ) :
    (cbil E a b).re = (fun u => (a u).re) ⬝ᵥ (E *ᵥ fun v => (b v).re) -
      (fun u => (a u).im) ⬝ᵥ (E *ᵥ fun v => (b v).im) := by
  rw [dot_mulVec_eq, dot_mulVec_eq, ← Finset.sum_sub_distrib]
  unfold cbil
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro u _
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro v _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem cbil_im (E : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℂ) :
    (cbil E a b).im = (fun u => (a u).re) ⬝ᵥ (E *ᵥ fun v => (b v).im) +
      (fun u => (a u).im) ⬝ᵥ (E *ᵥ fun v => (b v).re) := by
  rw [dot_mulVec_eq, dot_mulVec_eq, ← Finset.sum_add_distrib]
  unfold cbil
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl; intro u _
  rw [Complex.im_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro v _
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem sum4_pow8_le (x₁ x₂ x₃ x₄ K : ℝ) (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃) (h₄ : 0 ≤ x₄)
    (k₁ : x₁ ^ 8 ≤ K) (k₂ : x₂ ^ 8 ≤ K) (k₃ : x₃ ^ 8 ≤ K) (k₄ : x₄ ^ 8 ≤ K) :
    (x₁ + x₂ + x₃ + x₄) ^ 8 ≤ 4 ^ 8 * K := by
  have hmK : (max (max x₁ x₂) (max x₃ x₄)) ^ 8 ≤ K := by
    rcases max_choice (max x₁ x₂) (max x₃ x₄) with h | h <;> rw [h]
    · rcases max_choice x₁ x₂ with h' | h' <;> rw [h'] <;> assumption
    · rcases max_choice x₃ x₄ with h' | h' <;> rw [h'] <;> assumption
  set m := max (max x₁ x₂) (max x₃ x₄)
  have hm0 : 0 ≤ m := le_trans h₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hsum : x₁ + x₂ + x₃ + x₄ ≤ 4 * m := by
    have a1 : x₁ ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have a2 : x₂ ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have a3 : x₃ ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
    have a4 : x₄ ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  calc (x₁ + x₂ + x₃ + x₄) ^ 8 ≤ (4 * m) ^ 8 := pow_le_pow_left₀ (by linarith) hsum 8
    _ = 4 ^ 8 * m ^ 8 := by ring
    _ ≤ 4 ^ 8 * K := by gcongr

theorem cbil_pow8_le (E : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) :
    ‖cbil E a b‖ ^ 8 ≤ 4 ^ 8 * ((N : ℝ) ^ 8 * Matrix.trace ((E * Eᵀ) ^ 4)) := by
  have hre : ∀ (c : Fin N → ℂ), (∀ i, ‖c i‖ ≤ 1) → ∀ i, |(c i).re| ≤ 1 :=
    fun c hc i => (Complex.abs_re_le_norm _).trans (hc i)
  have him : ∀ (c : Fin N → ℂ), (∀ i, ‖c i‖ ≤ 1) → ∀ i, |(c i).im| ≤ 1 :=
    fun c hc i => (Complex.abs_im_le_norm _).trans (hc i)
  set ar : Fin N → ℝ := fun u => (a u).re
  set ai : Fin N → ℝ := fun u => (a u).im
  set br : Fin N → ℝ := fun v => (b v).re
  set bi : Fin N → ℝ := fun v => (b v).im
  have k : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 1) → (∀ i, |y i| ≤ 1) →
      |x ⬝ᵥ (E *ᵥ y)| ^ 8 ≤ (N : ℝ) ^ 8 * Matrix.trace ((E * Eᵀ) ^ 4) := by
    intro x y hx hy
    rw [show |x ⬝ᵥ (E *ᵥ y)| ^ 8 = (x ⬝ᵥ (E *ᵥ y)) ^ 8 by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_mul, sq_abs]]
    exact rbil_pow8_le E x y hx hy
  have hnorm : ‖cbil E a b‖ ≤ |ar ⬝ᵥ (E *ᵥ br)| + |ai ⬝ᵥ (E *ᵥ bi)| + |ar ⬝ᵥ (E *ᵥ bi)| + |ai ⬝ᵥ (E *ᵥ br)| := by
    calc ‖cbil E a b‖ ≤ |(cbil E a b).re| + |(cbil E a b).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        rw [cbil_re, cbil_im]
        have e1 := abs_sub (ar ⬝ᵥ (E *ᵥ br)) (ai ⬝ᵥ (E *ᵥ bi))
        have e2 := abs_add_le (ar ⬝ᵥ (E *ᵥ bi)) (ai ⬝ᵥ (E *ᵥ br))
        linarith
  calc ‖cbil E a b‖ ^ 8 ≤ (|ar ⬝ᵥ (E *ᵥ br)| + |ai ⬝ᵥ (E *ᵥ bi)| + |ar ⬝ᵥ (E *ᵥ bi)| +
        |ai ⬝ᵥ (E *ᵥ br)|) ^ 8 := pow_le_pow_left₀ (norm_nonneg _) hnorm 8
    _ ≤ _ := sum4_pow8_le _ _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
        (k ar br (hre a ha) (hre b hb)) (k ai bi (him a ha) (him b hb))
        (k ar bi (hre a ha) (him b hb)) (k ai br (him a ha) (hre b hb))

/-! ## The per-selector sampling error -/

noncomputable def sampleErr (D : Cell N → ℝ) (S : Fin Q → Cell N) (a b : Fin N → ℂ) : ℂ :=
  (∑ u, ∑ v, a u * b v * (D (u, v) : ℂ)) / (N : ℂ) ^ 2 - (∑ j, a (S j).1 * b (S j).2 * (D (S j) : ℂ)) / (Q : ℂ)

theorem sum_cell_indicator (f : Fin N → Fin N → ℂ) (s : Cell N) :
    ∑ u, ∑ v, f u v * ((if s = (u, v) then 1 else 0 : ℝ) : ℂ) = f s.1 s.2 := by
  rw [Finset.sum_eq_single s.1]
  · rw [Finset.sum_eq_single s.2]
    · simp
    · intro v _ hv
      have : s ≠ (s.1, v) := fun h => hv (by rw [h])
      simp [this]
    · simp
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    have : s ≠ (u, v) := fun h => hu (by rw [h])
    simp [this]
  · simp

theorem ecell_eq (D : Cell N → ℝ) (S : Fin Q → Cell N) (c : Cell N) :
    Ecell D S c = (Q : ℝ) * D c - (N : ℝ) ^ 2 * ∑ j, (if S j = c then 1 else 0) * D c := by
  unfold Ecell yc
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem sampleErr_eq (hQ : 0 < Q) (hN : 0 < N) (D : Cell N → ℝ) (S : Fin Q → Cell N) (a b : Fin N → ℂ) :
    sampleErr D S a b = cbil (errMatrix D S) a b / ((Q : ℂ) * (N : ℂ) ^ 2) := by
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set f : Fin N → Fin N → ℂ := fun u v => a u * b v * (D (u, v) : ℂ) with hf
  have hind : ∑ u, ∑ v, ∑ j, f u v * ((if S j = (u, v) then 1 else 0 : ℝ) : ℂ) =
      ∑ j, a (S j).1 * b (S j).2 * (D (S j) : ℂ) := by
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [sum_cell_indicator f (S j)]
  have hc : cbil (errMatrix D S) a b = (Q : ℂ) * ∑ u, ∑ v, f u v -
      (N : ℂ) ^ 2 * ∑ u, ∑ v, ∑ j, f u v * ((if S j = (u, v) then 1 else 0 : ℝ) : ℂ) := by
    unfold cbil errMatrix
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro v _
    rw [ecell_eq, hf]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
  rw [hc, hind, sampleErr]
  field_simp
  simp only [hf]
  ring

/-! ## The potential and finite Jensen -/

noncomputable def potential {Z T : Type} [Fintype Z] [Fintype T] (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) : ℝ :=
  ∑ z, ∑ t, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4)

theorem potential_nonneg {Z T : Type} [Fintype Z] [Fintype T] (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) :
    0 ≤ potential D S :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => trace_pow4_nonneg _

/-- Finite Jensen for the eighth power: `(E f)⁸ ≤ E f⁸` for `f ≥ 0`. -/
theorem uMean_pow8_le {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (uMean f) ^ 8 ≤ uMean fun ω => f ω ^ 8 := by
  unfold uMean
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (fun i _ => hf i) 7
  rw [Finset.card_univ] at h
  rw [div_pow, div_le_div_iff₀ (by positivity) hc]
  calc (∑ ω, f ω) ^ 8 * (Fintype.card Ω : ℝ) ≤ ((Fintype.card Ω : ℝ) ^ 7 * ∑ ω, f ω ^ 8) * Fintype.card Ω :=
        mul_le_mul_of_nonneg_right h hc.le
    _ = (∑ ω, f ω ^ 8) * (Fintype.card Ω : ℝ) ^ 8 := by ring

theorem universal_of_potential {Z T : Type} [Fintype Z] [Nonempty Z] [Fintype T] (hQ : 0 < Q) (hN : 0 < N)
    (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) (τ : Z → T) (a b : Z → Fin N → ℂ)
    (ha : ∀ z i, ‖a z i‖ ≤ 1) (hb : ∀ z i, ‖b z i‖ ≤ 1) :
    (uMean fun z => ‖sampleErr (D z (τ z)) S (a z) (b z)‖) ^ 8 ≤
      4 ^ 8 * potential D S / ((Fintype.card Z : ℝ) * (Q : ℝ) ^ 8 * (N : ℝ) ^ 8) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  set T' : Z → ℝ := fun z => Matrix.trace ((errMatrix (D z (τ z)) S * (errMatrix (D z (τ z)) S)ᵀ) ^ 4)
  have hpt : ∀ z, ‖sampleErr (D z (τ z)) S (a z) (b z)‖ ^ 8 ≤ 4 ^ 8 * T' z / ((Q : ℝ) ^ 8 * (N : ℝ) ^ 8) := by
    intro z
    rw [sampleErr_eq hQ hN, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast, div_pow,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := cbil_pow8_le (errMatrix (D z (τ z)) S) (a z) (b z) (ha z) (hb z)
    calc ‖cbil (errMatrix (D z (τ z)) S) (a z) (b z)‖ ^ 8 * ((Q : ℝ) ^ 8 * (N : ℝ) ^ 8)
        ≤ 4 ^ 8 * ((N : ℝ) ^ 8 * T' z) * ((Q : ℝ) ^ 8 * (N : ℝ) ^ 8) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 4 ^ 8 * T' z * ((Q : ℝ) * (N : ℝ) ^ 2) ^ 8 := by ring
  have hTle : ∑ z, T' z ≤ potential D S := by
    apply Finset.sum_le_sum; intro z _
    exact Finset.single_le_sum (f := fun t => Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4))
      (fun t _ => trace_pow4_nonneg _) (Finset.mem_univ (τ z))
  calc (uMean fun z => ‖sampleErr (D z (τ z)) S (a z) (b z)‖) ^ 8
      ≤ uMean fun z => ‖sampleErr (D z (τ z)) S (a z) (b z)‖ ^ 8 := uMean_pow8_le _ (fun z => norm_nonneg _)
    _ ≤ uMean fun z => 4 ^ 8 * T' z / ((Q : ℝ) ^ 8 * (N : ℝ) ^ 8) := uMean_mono hpt
    _ = 4 ^ 8 * (∑ z, T' z) / ((Fintype.card Z : ℝ) * (Q : ℝ) ^ 8 * (N : ℝ) ^ 8) := by
        unfold uMean
        rw [← Finset.sum_div, ← Finset.mul_sum]
        field_simp
    _ ≤ 4 ^ 8 * potential D S / ((Fintype.card Z : ℝ) * (Q : ℝ) ^ 8 * (N : ℝ) ^ 8) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hTle (by positivity)

/-! ## A list no worse than the mean -/

/-- The constant of the direct `h = 4` moment: `2⁸·5·8⁸` (`DirectMoment.sum_walkMoment_le_explicit` at `L = 8`). -/
def C8 : ℝ := 2 ^ 8 * 5 * 8 ^ 8

/-- **The expected potential over independent uniform lists** is `≤ |Z||T|·C₈Q⁴N¹³` (the direct moment bound,
`DirectMoment.sum_walkMoment_le_explicit` at `L = 8`, through `walkMoment_eq_trace`). -/
theorem uMean_potential_le {Z T : Type} [Fintype Z] [Fintype T] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Z → T → Cell N → ℝ) (hD : ∀ z t c, |D z t c| ≤ 1) :
    uMean (fun S : Fin Q → Cell N => potential D S) ≤
      (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13 := by
  classical
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcard : (Fintype.card (Fin Q → Cell N) : ℝ) = (N : ℝ) ^ (2 * Q) := by
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  have hsum : ∑ S : Fin Q → Cell N, potential D S ≤
      (Fintype.card Z : ℝ) * Fintype.card T * (C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13)) := by
    unfold potential
    rw [Finset.sum_comm]
    have hzt : ∀ z t, ∑ S : Fin Q → Cell N, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4) ≤
        C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13) := by
      intro z t
      have hw := sum_walkMoment_le_explicit (L := 8) (by norm_num) hN hNQ (D z t) (hD z t)
      simp_rw [walkMoment_eq_trace] at hw
      have e : 2 * Q + 2 * 8 + 1 - 8 / 2 = 2 * Q + 13 := by omega
      rw [e] at hw
      refine (le_abs_self _).trans (hw.trans (le_of_eq ?_))
      unfold C8
      norm_num
    calc ∑ z, ∑ S : Fin Q → Cell N, ∑ t, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4)
        = ∑ z, ∑ t, ∑ S : Fin Q → Cell N, Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4) := by
          apply Finset.sum_congr rfl; intro z _; rw [Finset.sum_comm]
      _ ≤ ∑ _z : Z, ∑ _t : T, C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ (2 * Q + 13) :=
          Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun t _ => hzt z t
      _ = _ := by simp; ring
  unfold uMean
  rw [hcard, div_le_iff₀ (by positivity)]
  refine hsum.trans (le_of_eq ?_)
  rw [pow_add, pow_mul]; ring

theorem exists_potential_le {Z T : Type} [Fintype Z] [Fintype T] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Z → T → Cell N → ℝ) (hD : ∀ z t c, |D z t c| ≤ 1) :
    ∃ S : Fin Q → Cell N,
      potential D S ≤ (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13 := by
  classical
  haveI : Nonempty (Cell N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hmean := uMean_potential_le hN hNQ D hD
  unfold uMean at hmean
  have hc : (0 : ℝ) < Fintype.card (Fin Q → Cell N) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc] at hmean
  obtain ⟨S, _, hS⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin Q → Cell N)))
    Finset.univ_nonempty (f := fun S => potential D S)
    (g := fun _ => (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith)
  exact ⟨S, hS⟩

theorem universal_of_potential_le {Z T : Type} [Fintype Z] [Nonempty Z] [Fintype T] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N)
    (hS : potential D S ≤ (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13)
    (η : ℝ) (hη : 0 ≤ η) (hQη : 4 ^ 8 * C8 * Fintype.card T * (N : ℝ) ^ 5 ≤ (Q : ℝ) ^ 4 * η ^ 8)
    (τ : Z → T) (a b : Z → Fin N → ℂ) (ha : ∀ z i, ‖a z i‖ ≤ 1) (hb : ∀ z i, ‖b z i‖ ≤ 1) :
    (uMean fun z => ‖sampleErr (D z (τ z)) S (a z) (b z)‖) ≤ η := by
  have hQ : 0 < Q := lt_of_lt_of_le (by omega) hNQ
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have h8 := universal_of_potential hQ hN0 D S τ a b ha hb
  have hbound : 4 ^ 8 * potential D S / ((Fintype.card Z : ℝ) * (Q : ℝ) ^ 8 * (N : ℝ) ^ 8) ≤ η ^ 8 := by
    rw [div_le_iff₀ (by positivity)]
    calc 4 ^ 8 * potential D S ≤ 4 ^ 8 * ((Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (Fintype.card Z : ℝ) * (Q : ℝ) ^ 4 * (N : ℝ) ^ 8 * (4 ^ 8 * C8 * Fintype.card T * (N : ℝ) ^ 5) := by ring
      _ ≤ (Fintype.card Z : ℝ) * (Q : ℝ) ^ 4 * (N : ℝ) ^ 8 * ((Q : ℝ) ^ 4 * η ^ 8) :=
          mul_le_mul_of_nonneg_left hQη (by positivity)
      _ = η ^ 8 * ((Fintype.card Z : ℝ) * (Q : ℝ) ^ 8 * (N : ℝ) ^ 8) := by ring
  have hmean0 : 0 ≤ uMean fun z => ‖sampleErr (D z (τ z)) S (a z) (b z)‖ := by
    unfold uMean; exact div_nonneg (Finset.sum_nonneg fun z _ => norm_nonneg _) (Nat.cast_nonneg _)
  exact (pow_le_pow_iff_left₀ hmean0 hη (by norm_num : (8 : ℕ) ≠ 0)).mp (h8.trans hbound)

theorem samp_universal {Z T : Type} [Fintype Z] [Nonempty Z] [Fintype T] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Z → T → Cell N → ℝ) (hD : ∀ z t c, |D z t c| ≤ 1) (η : ℝ) (hη : 0 ≤ η)
    (hQη : 4 ^ 8 * C8 * Fintype.card T * (N : ℝ) ^ 5 ≤ (Q : ℝ) ^ 4 * η ^ 8) :
    ∃ S : Fin Q → Cell N, ∀ (τ : Z → T) (a b : Z → Fin N → ℂ), (∀ z i, ‖a z i‖ ≤ 1) → (∀ z i, ‖b z i‖ ≤ 1) →
      (uMean fun z => ‖sampleErr (D z (τ z)) S (a z) (b z)‖) ≤ η := by
  obtain ⟨S, hS⟩ := exists_potential_le hN hNQ D hD
  exact ⟨S, fun τ a b ha hb => universal_of_potential_le hN hNQ D S hS η hη hQη τ a b ha hb⟩

end NearCubicWires.WireExponent3_5.Sampler

import Proof.Wire_3_5.FilterGapParity

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SupplierPipeline Finset

section Moments
variable {Ω : Type} [Fintype Ω]

theorem sum_fin_cons (N : ℕ) (F : (Fin (N + 1) → Ω) → ℝ) :
    ∑ s, F s = ∑ ω : Ω, ∑ s' : Fin N → Ω, F (Fin.cons ω s') := by
  rw [← (Fin.consEquiv fun _ => Ω).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The centred count of `N` copies. -/
def centredCount (Y : Ω → ℝ) (N : ℕ) (s : Fin N → Ω) : ℝ := ∑ j, Y (s j)

omit [Fintype Ω] in
theorem centredCount_cons (Y : Ω → ℝ) (N : ℕ) (ω : Ω) (s : Fin N → Ω) :
    centredCount Y (N + 1) (Fin.cons ω s) = Y ω + centredCount Y N s := by
  simp [centredCount, Fin.sum_univ_succ]

theorem sum_const_fun (N : ℕ) (a : ℝ) :
    (∑ _s : Fin N → Ω, a) = (Fintype.card Ω : ℝ) ^ N * a := by
  simp [Finset.sum_const, Finset.card_univ]

theorem sum_sum_left (N : ℕ) (f : Ω → ℝ) :
    ∑ ω, ∑ _s : Fin N → Ω, f ω = (Fintype.card Ω : ℝ) ^ N * ∑ ω, f ω := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ω _ => by rw [sum_const_fun]

theorem sum_sum_right (N : ℕ) (h : (Fin N → Ω) → ℝ) :
    ∑ _ω : Ω, ∑ s, h s = (Fintype.card Ω : ℝ) * ∑ s, h s := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_sum_mul (N : ℕ) (k : ℝ) (f : Ω → ℝ) (h : (Fin N → Ω) → ℝ) :
    ∑ ω, ∑ s, k * (f ω * h s) = k * ((∑ ω, f ω) * ∑ s, h s) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]

/-- `Σ_s T = 0` for a centred `Y`. -/
theorem sum_centredCount (Y : Ω → ℝ) (hY : ∑ ω, Y ω = 0) (N : ℕ) :
    ∑ s : Fin N → Ω, centredCount Y N s = 0 := by
  induction N with
  | zero => simp [centredCount]
  | succ N ih =>
    rw [sum_fin_cons]
    simp only [centredCount_cons, Finset.sum_add_distrib, sum_sum_left, hY, mul_zero, zero_add]
    rw [sum_sum_right, ih, mul_zero]

/-- `c·Σ_s T² = N·A₂·c^N`. -/
theorem sum_centredCount_sq (Y : Ω → ℝ) (hY : ∑ ω, Y ω = 0) (N : ℕ) :
    (Fintype.card Ω : ℝ) * ∑ s : Fin N → Ω, centredCount Y N s ^ 2 =
      N * (∑ ω, Y ω ^ 2) * (Fintype.card Ω : ℝ) ^ N := by
  induction N with
  | zero => simp [centredCount]
  | succ N ih =>
    rw [sum_fin_cons]
    have hexp : ∀ ω (s : Fin N → Ω), centredCount Y (N + 1) (Fin.cons ω s) ^ 2 =
        Y ω ^ 2 + 2 * (Y ω * centredCount Y N s) + centredCount Y N s ^ 2 := by
      intro ω s; rw [centredCount_cons]; ring
    simp only [hexp, Finset.sum_add_distrib, sum_sum_left, sum_sum_right, sum_sum_mul,
      sum_centredCount Y hY N, hY]
    push_cast
    linear_combination (Fintype.card Ω : ℝ) * ih

/-- **The exact fourth central moment**: `c²·Σ_s T⁴ = c^N(N·c·A₄ + 3N(N−1)A₂²)`. -/
theorem sum_centred_pow_four (Y : Ω → ℝ) (hY : ∑ ω, Y ω = 0) (N : ℕ) :
    (Fintype.card Ω : ℝ) ^ 2 * ∑ s : Fin N → Ω, centredCount Y N s ^ 4 =
      (Fintype.card Ω : ℝ) ^ N *
        (N * (Fintype.card Ω : ℝ) * (∑ ω, Y ω ^ 4) + 3 * N * (N - 1) * (∑ ω, Y ω ^ 2) ^ 2) := by
  induction N with
  | zero => simp [centredCount]
  | succ N ih =>
    rw [sum_fin_cons]
    have hexp : ∀ ω (s : Fin N → Ω), centredCount Y (N + 1) (Fin.cons ω s) ^ 4 =
        Y ω ^ 4 + 4 * (Y ω ^ 3 * centredCount Y N s) + 6 * (Y ω ^ 2 * centredCount Y N s ^ 2) +
          4 * (Y ω * centredCount Y N s ^ 3) + centredCount Y N s ^ 4 := by
      intro ω s; rw [centredCount_cons]; ring
    have h2 := sum_centredCount_sq Y hY N
    simp only [hexp, Finset.sum_add_distrib, sum_sum_left, sum_sum_right, sum_sum_mul,
      sum_centredCount Y hY N, hY]
    push_cast
    linear_combination (6 * (Fintype.card Ω : ℝ) * ∑ ω, Y ω ^ 2) * h2 + (Fintype.card Ω : ℝ) * ih

end Moments

/-! ## The two tails of the `128`-copy count -/

section Tails
variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- The centred indicator `Y = [g] − q`, `q = Pr[g]`. -/
noncomputable def centredBit (g : Ω → Bool) (ω : Ω) : ℝ := bitAsReal (g ω) - booleanMean g

theorem sum_centredBit (g : Ω → Bool) : ∑ ω, centredBit g ω = 0 := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [centredBit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, booleanMean]
  field_simp
  ring

theorem sum_centredBit_sq (g : Ω → Bool) :
    ∑ ω, centredBit g ω ^ 2 = Fintype.card Ω * (booleanMean g * (1 - booleanMean g)) := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hb : ∀ ω, bitAsReal (g ω) ^ 2 = bitAsReal (g ω) := by intro ω; cases g ω <;> simp [bitAsReal]
  have : ∀ ω, centredBit g ω ^ 2 = bitAsReal (g ω) * (1 - 2 * booleanMean g) + booleanMean g ^ 2 := by
    intro ω; simp only [centredBit]; nlinarith [hb ω]
  simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : (∑ ω, bitAsReal (g ω)) = Fintype.card Ω * booleanMean g := by
    unfold booleanMean; field_simp
  rw [hsum]; ring

theorem centredBit_pow_four_le (g : Ω → Bool) (ω : Ω) : centredBit g ω ^ 4 ≤ centredBit g ω ^ 2 := by
  have h0 : 0 ≤ booleanMean g := by
    unfold booleanMean; exact div_nonneg (Finset.sum_nonneg fun ω _ => by cases g ω <;> simp [bitAsReal])
      (by positivity)
  have h1 : booleanMean g ≤ 1 := by
    unfold booleanMean
    rw [div_le_one (Nat.cast_pos.mpr Fintype.card_pos)]
    calc (∑ ω, bitAsReal (g ω)) ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum fun ω _ => by
          cases g ω <;> simp [bitAsReal]
      _ = _ := by simp
  have hb : 0 ≤ bitAsReal (g ω) ∧ bitAsReal (g ω) ≤ 1 := by cases g ω <;> simp [bitAsReal]
  have habs : centredBit g ω ^ 2 ≤ 1 := by
    simp only [centredBit]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - (bitAsReal (g ω) - booleanMean g) by linarith)
      (show (0 : ℝ) ≤ bitAsReal (g ω) - booleanMean g + 1 by linarith)]
  have := sq_nonneg (centredBit g ω)
  calc centredBit g ω ^ 4 = (centredBit g ω ^ 2) * (centredBit g ω ^ 2) := by ring
    _ ≤ 1 * (centredBit g ω ^ 2) := mul_le_mul_of_nonneg_right habs this
    _ = _ := one_mul _

omit [Nonempty Ω] in
/-- The copy count as the centred sum: `#{j : g(s_j)} = T(s) + Nq`. -/
theorem card_filter_eq (g : Ω → Bool) (N : ℕ) (s : Fin N → Ω) :
    ((univ.filter fun j => g (s j) = true).card : ℝ) = centredCount (centredBit g) N s + N * booleanMean g := by
  simp only [centredCount, centredBit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, sub_add_cancel]
  rw [Finset.card_filter]; push_cast
  simp [bitAsReal]

/-- `E_s T⁴ ≤ N·q(1−q) + 3N(N−1)(q(1−q))²`. -/
theorem mean_centred_pow_four_le (g : Ω → Bool) (N : ℕ) :
    (∑ s : Fin N → Ω, centredCount (centredBit g) N s ^ 4) / (Fintype.card Ω : ℝ) ^ N ≤
      N * (booleanMean g * (1 - booleanMean g)) +
        3 * N * (N - 1) * (booleanMean g * (1 - booleanMean g)) ^ 2 := by
  set c : ℝ := (Fintype.card Ω : ℝ)
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  have hid := sum_centred_pow_four (centredBit g) (sum_centredBit g) N
  rw [sum_centredBit_sq] at hid
  have h4 : ∑ ω, centredBit g ω ^ 4 ≤ c * (booleanMean g * (1 - booleanMean g)) := by
    rw [← sum_centredBit_sq]; exact Finset.sum_le_sum fun ω _ => centredBit_pow_four_le g ω
  rw [div_le_iff₀ (by positivity)]
  have hcN : 0 < c ^ N := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  -- divide the identity by c²
  have key : c ^ 2 * ∑ s : Fin N → Ω, centredCount (centredBit g) N s ^ 4 ≤
      c ^ 2 * ((N * (booleanMean g * (1 - booleanMean g)) +
        3 * N * (N - 1) * (booleanMean g * (1 - booleanMean g)) ^ 2) * c ^ N) := by
    rw [hid]
    have : (N : ℝ) * c * ∑ ω, centredBit g ω ^ 4 ≤ N * c * (c * (booleanMean g * (1 - booleanMean g))) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- Markov on the fourth moment: `Pr[|T| ≥ d] ≤ E T⁴/d⁴`. -/
theorem prob_le_of_pow_four (g : Ω → Bool) (N : ℕ) (ev : (Fin N → Ω) → Bool) {d : ℝ} (hd : 0 < d)
    (hev : ∀ s, ev s = true → d ^ 4 ≤ centredCount (centredBit g) N s ^ 4) :
    booleanMean ev ≤ ((∑ s : Fin N → Ω, centredCount (centredBit g) N s ^ 4) / (Fintype.card Ω : ℝ) ^ N) / d ^ 4 := by
  unfold booleanMean
  rw [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpt : ∀ s, bitAsReal (ev s) * d ^ 4 ≤ centredCount (centredBit g) N s ^ 4 := by
    intro s
    by_cases h : ev s = true
    · simp only [h, bitAsReal, if_true, one_mul]; exact hev s h
    · simp only [Bool.not_eq_true] at h; simp only [h, bitAsReal]; simp; positivity
  have := Finset.sum_le_sum fun s (_ : s ∈ (univ : Finset (Fin N → Ω))) => hpt s
  rw [← Finset.sum_mul] at this
  have hc : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) ^ N := by positivity
  nlinarith

theorem count_tail_low (g : Ω → Bool) (hq : booleanMean g ≤ 1 / 64) :
    booleanMean (fun s : Fin 128 → Ω => decide (32 < (univ.filter fun j => g (s j) = true).card)) ≤ 1 / 128 := by
  set q := booleanMean g
  have hq0 : 0 ≤ q := by
    simp only [q, booleanMean]; exact div_nonneg (Finset.sum_nonneg fun ω _ => by cases g ω <;> simp [bitAsReal])
      (by positivity)
  refine (prob_le_of_pow_four g 128 _ (d := 31) (by norm_num) ?_).trans ?_
  · intro s hs
    simp only [decide_eq_true_eq] at hs
    have hc := card_filter_eq g 128 s
    have h33 : (33 : ℝ) ≤ ((univ.filter fun j => g (s j) = true).card : ℝ) := by exact_mod_cast hs
    have hT : 31 ≤ centredCount (centredBit g) 128 s := by push_cast at hc; linarith
    exact pow_le_pow_left₀ (by norm_num) hT 4
  · have hm := mean_centred_pow_four_le g 128
    have hv : q * (1 - q) ≤ 1 / 64 := by nlinarith
    have hv0 : 0 ≤ q * (1 - q) := by nlinarith
    rw [div_le_iff₀ (by norm_num)]
    push_cast at hm
    nlinarith

theorem count_tail_high (g : Ω → Bool) (hq : 6 / 13 ≤ booleanMean g) :
    booleanMean (fun s : Fin 128 → Ω => decide ((univ.filter fun j => g (s j) = true).card ≤ 32)) ≤ 1 / 128 := by
  set q := booleanMean g
  refine (prob_le_of_pow_four g 128 _ (d := 352 / 13) (by norm_num) ?_).trans ?_
  · intro s hs
    simp only [decide_eq_true_eq] at hs
    have hc := card_filter_eq g 128 s
    have h32 : ((univ.filter fun j => g (s j) = true).card : ℝ) ≤ 32 := by exact_mod_cast hs
    have hT : centredCount (centredBit g) 128 s ≤ -(352 / 13) := by push_cast at hc; linarith
    have habs : 352 / 13 ≤ |centredCount (centredBit g) 128 s| := by
      rw [abs_of_neg (by linarith)]; linarith
    calc (352 / 13 : ℝ) ^ 4 ≤ |centredCount (centredBit g) 128 s| ^ 4 := pow_le_pow_left₀ (by norm_num) habs 4
      _ = _ := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  · have hm := mean_centred_pow_four_le g 128
    have hv : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
    have hv0 : 0 ≤ q * (1 - q) := by
      have h1 : q ≤ 1 := by
        simp only [q, booleanMean]
        rw [div_le_one (Nat.cast_pos.mpr Fintype.card_pos)]
        calc (∑ ω, bitAsReal (g ω)) ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum fun ω _ => by
              cases g ω <;> simp [bitAsReal]
          _ = _ := by simp
      nlinarith
    rw [div_le_iff₀ (by norm_num)]
    push_cast at hm
    nlinarith

end Tails

/-! ## The base filter (the `128`-copy threshold) at the two endpoints -/

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `w(Z) ≤ U ⟹ Pr_s[the base filter rejects] ≤ 1/128`. -/
theorem baseFilter_reject_le (P : GapParams) (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0)
    (hK : 16 * P.len ≤ Fintype.card K) (Z : List Bool) (hZ : Z.length ≤ P.len) (hw : Z.count true ≤ P.cap) :
    booleanMean (fun s : BaseSeed P K => !baseFilter P (fieldOps Tr) s Z) ≤ 1 / 128 := by
  have h := count_tail_low (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z)
    (copyParity_prob_le_low P Tr hTr hK Z hZ hw)
  refine le_of_eq_of_le ?_ h
  congr 1; funext s
  simp only [baseFilter]
  rw [← decide_not]
  simp

/-- `w(Z) ≥ 4096U ⟹ Pr_s[the base filter accepts] ≤ 1/128`. -/
theorem baseFilter_accept_le (P : GapParams) (Tr : K →+ ZMod 2) (hTr : ∃ b, Tr b ≠ 0)
    (hK : 16 * P.len ≤ Fintype.card K) (hU : 1 ≤ P.cap) (Z : List Bool) (hZ : Z.length ≤ P.len)
    (hw : 4096 * P.cap ≤ Z.count true) :
    booleanMean (fun s : BaseSeed P K => baseFilter P (fieldOps Tr) s Z) ≤ 1 / 128 :=
  count_tail_high (fun c : CopySeed P K => copyParity P (fieldOps Tr) c Z)
    (copyParity_prob_ge_high P Tr hTr hK hU Z hZ hw)

end NearCubicWires.WireExponent3_5.Filters

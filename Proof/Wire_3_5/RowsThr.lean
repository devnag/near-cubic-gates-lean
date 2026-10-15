import Proof.Foundations.SupplierPipeline
import Proof.Wire_3_5.RowsSym
import Proof.Wire_3_5.MaskedExpectation

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Shared ZMod Finset

section Modular
variable {p : ℕ} [NeZero p]

def thrReported (A B : ℤ) (s : ZMod p) : Bool := decide ((A : ZMod p) + B + s = 0)

/-- **`row:modular-fourier`**: `1[A + B + s ≡ 0] = Σ_ℓ ((1/p)ω^{ℓs})·ω^{ℓA}·ω^{ℓB}`. -/
theorem thrReported_separable (A B : ℤ) (s : ZMod p) :
    bitC (thrReported A B s) = ∑ ℓ : ZMod p, ((p : ℂ)⁻¹ * chi (ℓ * s)) * chi (ℓ * (A : ZMod p)) * chi (ℓ * (B : ZMod p)) := by
  have h := indicator_eq_sum ((A : ZMod p) + (B : ZMod p) + s)
  unfold thrReported bitC
  rw [show (if decide ((A : ZMod p) + (B : ZMod p) + s = 0) = true then (1 : ℂ) else 0) =
    if (A : ZMod p) + (B : ZMod p) + s = 0 then 1 else 0 by simp, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [show ℓ * ((A : ZMod p) + (B : ZMod p) + s) = ℓ * s + ℓ * (A : ZMod p) + ℓ * (B : ZMod p) by ring, chi_add,
    chi_add]
  ring

theorem thrCoeff_mass (s : ZMod p) : ∑ ℓ : ZMod p, ‖(p : ℂ)⁻¹ * chi (ℓ * s)‖ = 1 := by
  simp only [norm_mul, norm_chi, mul_one, norm_inv, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

end Modular

section Radix
variable {ι : Type} [Fintype ι] {τ₀ K : ℕ}

def digitCount (v : ι → Fin τ₀ → ℕ) (Z : ι → Bool) (d : Fin τ₀) : ℕ := ∑ i, v i d * (Z i).toNat

/-- **The exact signed radix identity**: `Σ_i a_i(Z_i^+ − Z_i^−) = Σ_d b_0^d(T_d^+ − T_d^−)` when `a_i = Σ_d v_{i,d}b_0^d`. -/
theorem radix_signed_eq (b0 : ℕ) (a : ι → ℕ) (v : ι → Fin τ₀ → ℕ) (ha : ∀ i, a i = ∑ d, v i d * b0 ^ (d : ℕ))
    (Zp Zm : ι → Bool) :
    (∑ i, (a i : ℤ) * (((Zp i).toNat : ℤ) - (Zm i).toNat)) =
      ∑ d : Fin τ₀, (b0 : ℤ) ^ (d : ℕ) * ((digitCount v Zp d : ℤ) - digitCount v Zm d) := by
  calc (∑ i, (a i : ℤ) * (((Zp i).toNat : ℤ) - (Zm i).toNat))
      = ∑ i, ∑ d : Fin τ₀, (v i d : ℤ) * (b0 : ℤ) ^ (d : ℕ) * (((Zp i).toNat : ℤ) - (Zm i).toNat) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ha i]; push_cast; rw [Finset.sum_mul]
    _ = ∑ d : Fin τ₀, ∑ i, (v i d : ℤ) * (b0 : ℤ) ^ (d : ℕ) * (((Zp i).toNat : ℤ) - (Zm i).toNat) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [digitCount]
        push_cast
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The residue `Σ_d b_0^d(t_d^+ − t_d^−) (mod p)` of a signed digit tuple. -/
def tupleResidue (p b0 : ℕ) (tp tm : Fin τ₀ → ℕ) : ZMod p :=
  ((∑ d : Fin τ₀, (b0 : ℤ) ^ (d : ℕ) * ((tp d : ℤ) - tm d) : ℤ) : ZMod p)

def radixState (p b0 : ℕ) (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool) (s : ZMod p) : ℕ :=
  ∑ tup : Fin τ₀ → Fin (K + 1) × Fin (K + 1),
    if tupleResidue p b0 (fun d => ((tup d).1 : ℕ)) (fun d => ((tup d).2 : ℕ)) = s then
      ∏ d, (Pp d (tup d).1).toNat * (Pm d (tup d).2).toNat
    else 0

theorem radixState_of_oneHot (p b0 : ℕ) (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool) (tp tm : Fin τ₀ → Fin (K + 1))
    (hp : ∀ d t, Pp d t = decide (t = tp d)) (hm : ∀ d t, Pm d t = decide (t = tm d)) (s : ZMod p) :
    radixState p b0 Pp Pm s =
      if tupleResidue p b0 (fun d => (tp d : ℕ)) (fun d => (tm d : ℕ)) = s then 1 else 0 := by
  unfold radixState
  rw [Finset.sum_eq_single (fun d => (tp d, tm d))]
  · simp [hp, hm]
  · intro tup _ hne
    obtain ⟨d, hd⟩ : ∃ d, tup d ≠ (tp d, tm d) := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hz : (Pp d (tup d).1).toNat * (Pm d (tup d).2).toNat = 0 := by
      rw [hp, hm]
      by_cases h1 : (tup d).1 = tp d
      · have h2 : (tup d).2 ≠ tm d := fun h2 => hd (Prod.ext h1 h2)
        simp [h2]
      · simp [h1]
    split_ifs
    · exact Finset.prod_eq_zero (Finset.mem_univ d) hz
    · rfl
  · simp

theorem radixState_sum (p b0 : ℕ) [NeZero p] (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool) (tp tm : Fin τ₀ → Fin (K + 1))
    (hp : ∀ d t, Pp d t = decide (t = tp d)) (hm : ∀ d t, Pm d t = decide (t = tm d)) :
    ∑ s : ZMod p, radixState p b0 Pp Pm s = 1 := by
  simp only [radixState_of_oneHot p b0 Pp Pm tp tm hp hm]
  rw [Finset.sum_ite_eq]
  simp

def reportedThr (p b0 : ℕ) [NeZero p] (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool) (A B : ℤ) : ℕ :=
  ∑ s : ZMod p, radixState p b0 Pp Pm s * (thrReported A B s).toNat

theorem reportedThr_of_oneHot (p b0 : ℕ) [NeZero p] (Pp Pm : Fin τ₀ → Fin (K + 1) → Bool)
    (tp tm : Fin τ₀ → Fin (K + 1)) (hp : ∀ d t, Pp d t = decide (t = tp d)) (hm : ∀ d t, Pm d t = decide (t = tm d))
    (A B : ℤ) :
    reportedThr p b0 Pp Pm A B =
      (thrReported A B (tupleResidue p b0 (fun d => (tp d : ℕ)) (fun d => (tm d : ℕ)))).toNat := by
  unfold reportedThr
  simp only [radixState_of_oneHot p b0 Pp Pm tp tm hp hm, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem thrRow_eq_of_correct (p : ℕ) [NeZero p] (b0 : ℕ) (a : ι → ℕ) (v : ι → Fin τ₀ → ℕ)
    (ha : ∀ i, a i = ∑ d, v i d * b0 ^ (d : ℕ)) (Zp Zm : ι → Bool) (tp tm : Fin τ₀ → ℕ)
    (hp : ∀ d, tp d = digitCount v Zp d) (hm : ∀ d, tm d = digitCount v Zm d) (A B : ℤ) :
    thrReported A B (tupleResidue p b0 tp tm) =
      decide (((A + B + ∑ i, (a i : ℤ) * (((Zp i).toNat : ℤ) - (Zm i).toNat) : ℤ) : ZMod p) = 0) := by
  unfold thrReported tupleResidue
  rw [radix_signed_eq b0 a v ha Zp Zm]
  simp only [hp, hm, Int.cast_add]

end Radix

/-! ## Means -/

section Means
variable {Ω : Type} [Fintype Ω]

theorem uMean_sub' (f g : Ω → ℝ) : uMean (fun x => f x - g x) = uMean f - uMean g := by
  unfold uMean; rw [Finset.sum_sub_distrib, sub_div]

theorem uMean_const_mul (c : ℝ) (f : Ω → ℝ) : uMean (fun x => c * f x) = c * uMean f := by
  unfold uMean; rw [← Finset.mul_sum, mul_div_assoc]

theorem uMean_finsum {G : Type} [Fintype G] (f : G → Ω → ℝ) :
    uMean (fun x => ∑ g, f g x) = ∑ g, uMean (f g) := by
  unfold uMean; rw [Finset.sum_comm, Finset.sum_div]

theorem abs_uMean_le (f : Ω → ℝ) : |uMean f| ≤ uMean (fun x => |f x|) := by
  unfold uMean
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem uMean_le_const (f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ x, f x ≤ c) : uMean f ≤ c := by
  unfold uMean
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; exact hc
  · rw [div_le_iff₀ (Nat.cast_pos.mpr hpos)]
    calc ∑ x, f x ≤ ∑ _x : Ω, c := Finset.sum_le_sum fun x _ => hf x
      _ = c * Fintype.card Ω := by simp [mul_comm]

theorem uMean_swap' {Pr : Type} [Fintype Pr] (f : Pr → Ω → ℝ) :
    uMean (fun p => uMean (f p)) = uMean (fun x => uMean (fun p => f p x)) := by
  unfold uMean
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm, div_div, div_div, mul_comm (Fintype.card Ω : ℝ)]

end Means

section Prime
open NearCubicWires.SupplierPipeline

theorem prime_error_of_certificate {G Pr Ω : Type} [Fintype G] [Fintype Pr] (cert : PrimeSurrogateCertificate G Pr Ω)
    (C : Ω → Bool) (hsum : ∀ x, bitR (C x) = ∑ g, bitR (cert.exact g x)) (x : Ω) :
    bitR (C x) ≤ ∑ g, uMean (fun p => bitR (cert.modular g p x)) ∧
      ∑ g, uMean (fun p => bitR (cert.modular g p x)) ≤ bitR (C x) + Fintype.card G * cert.error := by
  have hPr : (0 : ℝ) < Fintype.card Pr := Nat.cast_pos.mpr cert.cardPositive
  have hper : ∀ g, bitR (cert.exact g x) ≤ uMean (fun p => bitR (cert.modular g p x)) ∧
      uMean (fun p => bitR (cert.modular g p x)) ≤ bitR (cert.exact g x) + cert.error := by
    intro g
    cases hex : cert.exact g x
    · have hs := cert.sound g x (by simp [hex])
      refine ⟨?_, ?_⟩
      · simp only [bitR, Bool.false_eq_true, if_false]
        exact div_nonneg (Finset.sum_nonneg fun p _ => bitR_nonneg _) hPr.le
      · simp only [bitR, Bool.false_eq_true, if_false, zero_add]
        exact hs
    · have hall : ∀ p, cert.modular g p x = true := cert.complete g x hex
      have hone : uMean (fun p => bitR (cert.modular g p x)) = 1 := by
        unfold uMean
        simp only [hall, bitR, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact div_self hPr.ne'
      rw [hone]
      exact ⟨le_of_eq (by simp [bitR]), by simp [bitR, cert.errorNonnegative]⟩
  rw [hsum]
  refine ⟨Finset.sum_le_sum fun g _ => (hper g).1, ?_⟩
  calc ∑ g, uMean (fun p => bitR (cert.modular g p x)) ≤ ∑ g, (bitR (cert.exact g x) + cert.error) :=
        Finset.sum_le_sum fun g _ => (hper g).2
    _ = ∑ g, bitR (cert.exact g x) + Fintype.card G * cert.error := by
        rw [Finset.sum_add_distrib]; simp

end Prime

section MaskedError
variable {Ω : Type} [Fintype Ω]

theorem masked_row_error {j : ℕ} (filt overCap : Fin j → Ω → Bool) (listFails reported truth : Ω → Bool) (δ ξ : ℝ)
    (hagree : ∀ ω, (∀ i, overCap i ω = false) → listFails ω = false → reported ω = truth ω)
    (hδ : uMean (fun ω => bitR (listFails ω && !decide (∃ i, overCap i ω = true))) ≤ δ)
    (hξ : ∀ i, uMean (fun ω => bitR (filt i ω && overCap i ω)) ≤ ξ) :
    uMean (fun ω => bitR (decide (∀ i, filt i ω = true)) * |bitR (reported ω) - bitR (truth ω)|) ≤ δ + j * ξ := by
  refine maskedRowError_holds (fun ω => decide (∀ i, filt i ω = true)) reported truth listFails
    (fun ω => decide (∃ i, overCap i ω = true)) δ (j * ξ) ?_ hδ ?_
  · intro ω hover hfail
    refine hagree ω (fun i => ?_) hfail
    simp only [decide_eq_false_iff_not, not_exists] at hover
    simpa using hover i
  · have hpt : ∀ ω, bitR (decide (∀ i, filt i ω = true) && decide (∃ i, overCap i ω = true)) ≤
        ∑ i, bitR (filt i ω && overCap i ω) := by
      intro ω
      cases h : (decide (∀ i, filt i ω = true) && decide (∃ i, overCap i ω = true))
      · simp only [bitR, Bool.false_eq_true, if_false]
        exact Finset.sum_nonneg fun i _ => bitR_nonneg _
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hall, i, hi⟩ := h
        calc bitR true = bitR (filt i ω && overCap i ω) := by simp [hall i, hi]
          _ ≤ ∑ i, bitR (filt i ω && overCap i ω) :=
            Finset.single_le_sum (f := fun i => bitR (filt i ω && overCap i ω)) (fun i _ => bitR_nonneg _)
              (Finset.mem_univ i)
    calc uMean (fun ω => bitR (decide (∀ i, filt i ω = true) && decide (∃ i, overCap i ω = true)))
        ≤ uMean (fun ω => ∑ i, bitR (filt i ω && overCap i ω)) := uMean_mono hpt
      _ = ∑ i, uMean (fun ω => bitR (filt i ω && overCap i ω)) := uMean_finsum _
      _ ≤ ∑ _i : Fin j, ξ := Finset.sum_le_sum fun i _ => hξ i
      _ = j * ξ := by simp

end MaskedError

section FullError
variable {Ω G Pr : Type} [Fintype Ω] [Fintype G] [Fintype Pr]

theorem thr_full_error (M C : Ω → Bool) (R Rhat : G → Pr → Ω → Bool) (ε δ' : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ')
    (hprime : ∀ x, bitR (C x) ≤ ∑ g, uMean (fun p => bitR (R g p x)) ∧
      ∑ g, uMean (fun p => bitR (R g p x)) ≤ bitR (C x) + ε)
    (hrow : ∀ g p, uMean (fun x => bitR (M x) * |bitR (Rhat g p x) - bitR (R g p x)|) ≤ δ') :
    |maskedMean M (fun x => bitR (C x)) -
        ∑ g, uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x)))| ≤ ε + Fintype.card G * δ' := by
  set Bv := ∑ g, uMean (fun p => maskedMean M (fun x => bitR (R g p x)))
  have hBv : Bv = uMean (fun x => bitR (M x) * ∑ g, uMean (fun p => bitR (R g p x))) := by
    simp only [Bv, maskedMean, Finset.mul_sum]
    rw [uMean_finsum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [uMean_swap' (fun p x => bitR (M x) * bitR (R g p x))]
    congr 1; funext x; rw [uMean_const_mul]
  have hAB : |maskedMean M (fun x => bitR (C x)) - Bv| ≤ ε := by
    rw [hBv]
    unfold maskedMean
    rw [← uMean_sub']
    refine (abs_uMean_le _).trans (uMean_le_const _ ε hε fun x => ?_)
    have hm0 := bitR_nonneg (M x)
    have hm1 := bitR_le_one (M x)
    obtain ⟨h1, h2⟩ := hprime x
    rw [← mul_sub, abs_mul, abs_of_nonneg hm0, abs_sub_comm, abs_of_nonneg (by linarith)]
    nlinarith
  have hBC : |Bv - ∑ g, uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x)))| ≤ Fintype.card G * δ' := by
    simp only [Bv]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ g, |uMean (fun p => maskedMean M (fun x => bitR (R g p x))) -
          uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x)))| ≤ ∑ _g : G, δ' := by
          refine Finset.sum_le_sum fun g _ => ?_
          rw [← uMean_sub']
          refine (abs_uMean_le _).trans (uMean_le_const _ δ' hδ fun p => ?_)
          unfold maskedMean
          rw [← uMean_sub']
          refine (abs_uMean_le _).trans ((le_of_eq ?_).trans (hrow g p))
          congr 1; funext x
          rw [← mul_sub, abs_mul, abs_of_nonneg (bitR_nonneg _), abs_sub_comm]
      _ = Fintype.card G * δ' := by simp
  calc _ = |(maskedMean M (fun x => bitR (C x)) - Bv) +
          (Bv - ∑ g, uMean (fun p => maskedMean M (fun x => bitR (Rhat g p x))))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε + Fintype.card G * δ' := add_le_add hAB hBC

theorem thr_full_error_masked {j : ℕ} (filt overCap : Fin j → Ω → Bool) (C : Ω → Bool) (R Rhat : G → Pr → Ω → Bool)
    (listFails : G → Pr → Ω → Bool) (ε δ ξ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hξ0 : 0 ≤ ξ)
    (hprime : ∀ x, bitR (C x) ≤ ∑ g, uMean (fun p => bitR (R g p x)) ∧
      ∑ g, uMean (fun p => bitR (R g p x)) ≤ bitR (C x) + ε)
    (hagree : ∀ g p ω, (∀ i, overCap i ω = false) → listFails g p ω = false → Rhat g p ω = R g p ω)
    (hδ : ∀ g p, uMean (fun ω => bitR (listFails g p ω && !decide (∃ i, overCap i ω = true))) ≤ δ)
    (hξ : ∀ i, uMean (fun ω => bitR (filt i ω && overCap i ω)) ≤ ξ) :
    |maskedMean (fun ω => decide (∀ i, filt i ω = true)) (fun x => bitR (C x)) -
        ∑ g, uMean (fun p => maskedMean (fun ω => decide (∀ i, filt i ω = true)) (fun x => bitR (Rhat g p x)))| ≤
      ε + Fintype.card G * (δ + j * ξ) :=
  thr_full_error _ C R Rhat ε (δ + j * ξ) hε (by positivity) hprime
    fun g p => masked_row_error filt overCap (listFails g p) (Rhat g p) (R g p) δ ξ (hagree g p) (hδ g p) hξ

end FullError

end NearCubicWires.WireExponent3_5.Rows

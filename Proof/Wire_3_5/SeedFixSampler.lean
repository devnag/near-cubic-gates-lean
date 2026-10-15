import Proof.Wire_3_5.FinalPassFused
import Proof.Wire_3_5.SamplerPrintable

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open scoped Matrix Matrix.Norms.L2Operator

/-! ## Norm domination for the operator norm -/

section OpNorm
variable {N : ℕ}

/-- `‖Eb‖² ≤ R²‖b‖²` with `R⁸ = tr((EEᵀ)⁴)` on real vectors (norm domination at `a = Eb`). -/
theorem mulVec_dot_le (E : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) :
    (E *ᵥ b) ⬝ᵥ (E *ᵥ b) ≤ ((Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ)) ^ 2 * (b ⬝ᵥ b) := by
  have hT : 0 ≤ Matrix.trace ((E * Eᵀ) ^ 4) := trace_pow4_nonneg E
  have hR8 : ((Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ)) ^ 8 = Matrix.trace ((E * Eᵀ) ^ 4) :=
    Real.rpow_inv_natCast_pow hT (by norm_num)
  have hR : 0 ≤ (Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ) := Real.rpow_nonneg hT _
  generalize (Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ) = R at hR8 hR ⊢
  have h := bilinear_pow8_le E (E *ᵥ b) b
  rw [trace_transpose_mul_pow, ← hR8] at h
  have hq : 0 ≤ (E *ᵥ b) ⬝ᵥ (E *ᵥ b) := dot_self_nonneg' _
  have hs : 0 ≤ b ⬝ᵥ b := dot_self_nonneg' _
  generalize (E *ᵥ b) ⬝ᵥ (E *ᵥ b) = q at h hq ⊢
  generalize b ⬝ᵥ b = s at h hs ⊢
  rcases hq.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hq4 : 0 < q ^ 4 := by positivity
    have h1 : q ^ 4 * q ^ 4 ≤ q ^ 4 * (R ^ 2 * s) ^ 4 := by
      calc q ^ 4 * q ^ 4 = q ^ 8 := by ring
        _ ≤ q ^ 4 * s ^ 4 * R ^ 8 := h
        _ = q ^ 4 * (R ^ 2 * s) ^ 4 := by ring
    exact (pow_le_pow_iff_left₀ hq (by positivity) (by norm_num)).mp (le_of_mul_le_mul_left h1 hq4)

theorem opNorm_le_trace (E : Matrix (Fin N) (Fin N) ℝ) :
    ‖E.map (fun r : ℝ => (r : ℂ))‖ ≤ (Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ) := by
  have hR : 0 ≤ (Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ) := Real.rpow_nonneg (trace_pow4_nonneg E) _
  have hdot := mulVec_dot_le E
  generalize (Matrix.trace ((E * Eᵀ) ^ 4)) ^ ((8 : ℕ)⁻¹ : ℝ) = R at hR hdot ⊢
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun x => ?_
  change ‖(EuclideanSpace.equiv (Fin N) ℂ).symm ((E.map fun r : ℝ => (r : ℂ)) *ᵥ x)‖ ≤ R * ‖x‖
  set y : EuclideanSpace ℂ (Fin N) := (EuclideanSpace.equiv (Fin N) ℂ).symm ((E.map fun r : ℝ => (r : ℂ)) *ᵥ x)
  set xr : Fin N → ℝ := fun v => (x v).re
  set xi : Fin N → ℝ := fun v => (x v).im
  have hy : ∀ u, y u = ∑ v, (E u v : ℂ) * x v := fun u => rfl
  have hre : ∀ u, (y u).re = (E *ᵥ xr) u := by
    intro u; rw [hy, Complex.re_sum]
    exact Finset.sum_congr rfl fun v _ => Complex.re_ofReal_mul _ _
  have him : ∀ u, (y u).im = (E *ᵥ xi) u := by
    intro u; rw [hy, Complex.im_sum]
    exact Finset.sum_congr rfl fun v _ => Complex.im_ofReal_mul _ _
  have hy2 : ‖y‖ ^ 2 = (E *ᵥ xr) ⬝ᵥ (E *ᵥ xr) + (E *ᵥ xi) ⬝ᵥ (E *ᵥ xi) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  have hx2 : ‖x‖ ^ 2 = xr ⬝ᵥ xr + xi ⬝ᵥ xi := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖y‖ ^ 2 ≤ (R * ‖x‖) ^ 2 := by
    rw [hy2, mul_pow, hx2]
    have := hdot xr
    have := hdot xi
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h2

end OpNorm

/-! ## `samp:moment`'s operator-norm conclusion from a potential bound -/

section Moment
variable {N Q : ℕ}

/-- The sampled error matrix of a real family is the complex cast of the real error matrix. -/
theorem sampleError_real (D : Cell N → ℝ) (S : Fin Q → Cell N) :
    sampleError (fun u v => (D (u, v) : ℂ)) S = (errMatrix D S).map (fun r : ℝ => (r : ℂ)) := by
  ext u v
  simp only [sampleError, Matrix.of_apply, Matrix.map_apply, errMatrix]
  rw [ecell_eq]
  push_cast
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem colMax_of_potential {Z T : Type} [Fintype Z] [Fintype T] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N)
    (hS : potential D S ≤ (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13)
    (η : ℝ) (hη : 0 ≤ η) (hQη : C8 * Fintype.card T * (N : ℝ) ^ 5 ≤ (Q : ℝ) ^ 4 * η ^ 8) :
    ∃ ηz : Z → ℝ, (∀ z t, ‖sampleError (fun u v => (D z t (u, v) : ℂ)) S‖ / ((Q : ℝ) * N) ≤ ηz z) ∧
      uMean ηz ≤ η := by
  have hQ : 0 < Q := lt_of_lt_of_le (by omega) hNQ
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  set Tz : Z → T → ℝ := fun z t => Matrix.trace ((errMatrix (D z t) S * (errMatrix (D z t) S)ᵀ) ^ 4) with hTz
  have hT0 : ∀ z t, 0 ≤ Tz z t := fun z t => trace_pow4_nonneg _
  have hsum0 : ∀ z, 0 ≤ ∑ t, Tz z t := fun z => Finset.sum_nonneg fun t _ => hT0 z t
  refine ⟨fun z => (∑ t, Tz z t) ^ ((8 : ℕ)⁻¹ : ℝ) / ((Q : ℝ) * N), fun z t => ?_, ?_⟩
  · rw [sampleError_real]
    apply div_le_div_of_nonneg_right _ (by positivity)
    refine (opNorm_le_trace _).trans (Real.rpow_le_rpow (hT0 z t) ?_ (by positivity))
    exact Finset.single_le_sum (f := fun t => Tz z t) (fun t _ => hT0 z t) (Finset.mem_univ t)
  · rcases isEmpty_or_nonempty Z with hZ | hZ
    · simp [uMean, hη]
    have hZr : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
    have hηz0 : ∀ z, 0 ≤ (∑ t, Tz z t) ^ ((8 : ℕ)⁻¹ : ℝ) / ((Q : ℝ) * N) :=
      fun z => div_nonneg (Real.rpow_nonneg (hsum0 z) _) (by positivity)
    have hpow : ∀ z, ((∑ t, Tz z t) ^ ((8 : ℕ)⁻¹ : ℝ) / ((Q : ℝ) * N)) ^ 8 = (∑ t, Tz z t) / ((Q : ℝ) * N) ^ 8 := by
      intro z; rw [div_pow, Real.rpow_inv_natCast_pow (hsum0 z) (by norm_num)]
    have hmean8 : uMean (fun z => (∑ t, Tz z t) / ((Q : ℝ) * N) ^ 8) =
        potential D S / ((Fintype.card Z : ℝ) * ((Q : ℝ) * N) ^ 8) := by
      unfold uMean potential
      rw [← Finset.sum_div, div_div, mul_comm (((Q : ℝ) * N) ^ 8)]
    have hbound : potential D S / ((Fintype.card Z : ℝ) * ((Q : ℝ) * N) ^ 8) ≤ η ^ 8 := by
      rw [div_le_iff₀ (by positivity)]
      calc potential D S ≤ (Fintype.card Z : ℝ) * Fintype.card T * C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13 := hS
        _ = (Fintype.card Z : ℝ) * (Q : ℝ) ^ 4 * (N : ℝ) ^ 8 * (C8 * Fintype.card T * (N : ℝ) ^ 5) := by ring
        _ ≤ (Fintype.card Z : ℝ) * (Q : ℝ) ^ 4 * (N : ℝ) ^ 8 * ((Q : ℝ) ^ 4 * η ^ 8) :=
            mul_le_mul_of_nonneg_left hQη (by positivity)
        _ = η ^ 8 * ((Fintype.card Z : ℝ) * ((Q : ℝ) * N) ^ 8) := by ring
    have h8 : (uMean fun z => (∑ t, Tz z t) ^ ((8 : ℕ)⁻¹ : ℝ) / ((Q : ℝ) * N)) ^ 8 ≤ η ^ 8 := by
      refine (uMean_pow8_le _ hηz0).trans ?_
      simp only [hpow]
      rw [hmean8]
      exact hbound
    have hm0 : 0 ≤ uMean fun z => (∑ t, Tz z t) ^ ((8 : ℕ)⁻¹ : ℝ) / ((Q : ℝ) * N) := by
      unfold uMean; exact div_nonneg (Finset.sum_nonneg fun z _ => hηz0 z) (Nat.cast_nonneg _)
    exact (pow_le_pow_iff_left₀ hm0 hη (by norm_num)).mp h8

end Moment

/-! ## The greedy seed, computable -/

section Greedy
variable {Z T : Type} [Fintype Z] [Fintype T]

/-- The number whose binary digits are the bits of a seed (bit `j` is `s j`). -/
def bitsNum : (m : ℕ) → (Fin m → Bool) → ℕ
  | 0, _ => 0
  | m + 1, s => Nat.bit (s 0) (bitsNum m fun j => s j.succ)

theorem testBit_bitsNum : ∀ (m : ℕ) (s : Fin m → Bool) (j : ℕ),
    (bitsNum m s).testBit j = if h : j < m then s ⟨j, h⟩ else false
  | 0, s, j => by simp [bitsNum]
  | m + 1, s, 0 => by simp [bitsNum]
  | m + 1, s, j + 1 => by
    rw [bitsNum, Nat.testBit_bit_succ, testBit_bitsNum m _ j]
    by_cases h : j < m
    · rw [dif_pos h, dif_pos (by omega)]; rfl
    · rw [dif_neg h, dif_neg (by omega)]

theorem bitsNum_eq_ofBits (m : ℕ) (s : Fin m → Bool) : bitsNum m s = ofBits s := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitsNum]
  by_cases h : j < m
  · rw [dif_pos h, testBit_ofBits s j h]
  · rw [dif_neg h]
    have hlt : ofBits s < 2 ^ m := ofVec_lt _
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

def posC (P : SeedParams) (seed : ℕ) (j : Fin P.Q) : Cell P.N :=
  P.cellEquiv (fun b => GF.bitF ((JoinElimination.gen P.modulus P.ell 8 seed j).testBit b))

theorem posC_eq (P : SeedParams) (seed : ℕ) : posC P seed = P.pos (decodeNat P seed) :=
  funext fun j => (pos_eq_gen P seed j).symm

/-- The sampled error matrix of a Boolean matrix, over `ℚ`: `E(u,v) = D(u,v)·Σ_j(1 − N²[S_j = (u,v)])`. -/
def errQ {N Q : ℕ} (D : Cell N → Bool) (S : Fin Q → Cell N) : Matrix (Fin N) (Fin N) ℚ :=
  fun u v => bitQ (D (u, v)) * ∑ j, (1 - (N : ℚ) ^ 2 * (if S j = (u, v) then 1 else 0))

/-- **The potential, exactly**: `Σ_zΣ_t tr((E_t(z)E_t(z)ᵀ)⁴)` over `ℚ`. -/
def potQ {N Q : ℕ} (D : Z → T → Cell N → Bool) (S : Fin Q → Cell N) : ℚ :=
  ∑ z, ∑ t, Matrix.trace ((errQ (D z t) S * (errQ (D z t) S)ᵀ) ^ 4)

theorem errQ_cast {N Q : ℕ} (D : Cell N → Bool) (S : Fin Q → Cell N) :
    (errQ D S).map (Rat.castHom ℝ) = errMatrix (fun c => bitR (D c)) S := by
  ext u v
  simp only [Matrix.map_apply, errQ, errMatrix, Ecell, yc, Rat.coe_castHom]
  push_cast
  rw [bitQ_cast]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem map_pow_cast {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) :
    ∀ k : ℕ, (M ^ k).map (Rat.castHom ℝ) = (M.map (Rat.castHom ℝ)) ^ k
  | 0 => by simp
  | k + 1 => by rw [pow_succ, pow_succ, Matrix.map_mul, map_pow_cast M k]

theorem potQ_cast {N Q : ℕ} (D : Z → T → Cell N → Bool) (S : Fin Q → Cell N) :
    ((potQ D S : ℚ) : ℝ) = potential (fun z t c => bitR (D z t c)) S := by
  unfold potQ potential
  push_cast
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  rw [← Rat.coe_castHom, AddMonoidHom.map_trace, map_pow_cast, Matrix.map_mul, Matrix.transpose_map, errQ_cast]

/-- The exact potential of a list of positions (the list is generated once; the objective reads each sample many
times). -/
def potQList {N : ℕ} (D : Z → T → Cell N → Bool) (L : List (Cell N)) : ℚ := potQ D fun j : Fin L.length => L.get j

theorem potQ_reindex {N Q Q' : ℕ} (D : Z → T → Cell N → Bool) (h : Q' = Q) (S : Fin Q → Cell N) :
    potQ D (fun j : Fin Q' => S (Fin.cast h j)) = potQ D S := by
  subst h
  rfl

theorem potQList_ofFn {N Q : ℕ} (D : Z → T → Cell N → Bool) (S : Fin Q → Cell N) :
    potQList D (List.ofFn S) = potQ D S := by
  unfold potQList
  simp only [List.get_ofFn]
  exact potQ_reindex D List.length_ofFn S

def greedyBitsQ (P : SeedParams) (D : Z → T → Cell P.N → Bool) : Fin (8 * P.ell) → Bool :=
  greedyQ (8 * P.ell) fun s => potQList D (List.ofFn (posC P (bitsNum _ s)))

/-- **The greedy sample list**: the positions of the greedy seed. -/
def greedySample (P : SeedParams) (D : Z → T → Cell P.N → Bool) : Fin P.Q → Cell P.N :=
  posC P (bitsNum _ (greedyBitsQ P D))

/-- **The rational greedy is the greedy of `samp:seed`** (`SamplerFix.samp_universal_greedy`'s seed). -/
theorem greedyBitsQ_eq (P : SeedParams) (D : Z → T → Cell P.N → Bool) :
    greedyBitsQ P D = greedy (8 * P.ell) fun s => potential (fun z t c => bitR (D z t c)) (P.pos (seedOfBits P s)) := by
  unfold greedyBitsQ
  rw [← greedy_cast]
  congr 1
  funext s
  rw [potQList_ofFn, potQ_cast, posC_eq, bitsNum_eq_ofBits]
  rfl

theorem greedySample_eq (P : SeedParams) (D : Z → T → Cell P.N → Bool) :
    greedySample P D = P.pos (seedOfBits P
      (greedy (8 * P.ell) fun s => potential (fun z t c => bitR (D z t c)) (P.pos (seedOfBits P s)))) := by
  unfold greedySample
  rw [greedyBitsQ_eq, posC_eq, bitsNum_eq_ofBits]
  rfl

theorem greedySample_good (P : SeedParams) (hNQ : P.N ≤ P.Q) (D : Z → T → Cell P.N → Bool) (η : ℝ) (hη : 0 ≤ η)
    (hQη : C8 * Fintype.card T * (P.N : ℝ) ^ 5 ≤ (P.Q : ℝ) ^ 4 * η ^ 8) :
    ∃ ηz : Z → ℝ, (∀ z t, ‖sampleError (fun u v => ((bitR (D z t (u, v)) : ℝ) : ℂ)) (greedySample P D)‖ /
        ((P.Q : ℝ) * P.N) ≤ ηz z) ∧ uMean ηz ≤ η := by
  have hD : ∀ z t c, |bitR (D z t c)| ≤ 1 := fun z t c => by cases D z t c <;> simp [bitR]
  have hS : potential (fun z t c => bitR (D z t c)) (greedySample P D) ≤
      (Fintype.card Z : ℝ) * Fintype.card T * C8 * (P.Q : ℝ) ^ 4 * (P.N : ℝ) ^ 13 := by
    rw [greedySample_eq]
    exact (greedy_le_mean _ _).trans ((uMean_bits P _).le.trans ((uMean_potential_seed P _).le.trans
      (uMean_potential_le Nat.one_le_two_pow hNQ _ hD)))
  exact colMax_of_potential Nat.one_le_two_pow hNQ (fun z t c => bitR (D z t c)) _ hS η hη hQη

end Greedy

/-! ## The sample count at a call's target -/

theorem sampleCount_mass_rate (kh D n T M : ℕ) (hn : 1 ≤ n) (hM : 1 ≤ M) :
    C8 * (T : ℝ) * ((2 ^ kh : ℕ) : ℝ) ^ 5 ≤
      (sampleCount kh D n (T * M ^ 2 + 1) : ℝ) ^ 4 * ((n : ℝ) ^ (-(D : ℝ)) / M) ^ 8 := by
  rw [rpow_neg_eq n D]
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (0 : ℝ) < (n : ℝ) ^ D := pow_pos (by linarith) D
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  set a : ℝ := (2 : ℝ) ^ ((5 * kh + 3) / 4) with ha
  set b : ℝ := (2 : ℝ) ^ kh with hb
  set x : ℝ := (n : ℝ) ^ D with hxdef
  set J : ℝ := (T : ℝ) * (M : ℝ) ^ 2 + 1 with hJ
  have hQ : (sampleCount kh D n (T * M ^ 2 + 1) : ℝ) = a * (2 ^ 13 * J * x ^ 2) := by
    unfold sampleCount; push_cast
    rw [show (n : ℝ) ^ (2 * D) = x ^ 2 by rw [hxdef, ← pow_mul, mul_comm], ha, hJ]
    ring
  have hbN : (((2 ^ kh : ℕ) : ℝ)) = b := by push_cast; exact hb.symm
  have h2 : b ^ 5 ≤ a ^ 4 := by
    rw [hb, ha, ← pow_mul, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hR : (a * (2 ^ 13 * J * x ^ 2)) ^ 4 * (1 / x / (M : ℝ)) ^ 8 = a ^ 4 * 2 ^ 52 * J ^ 4 / (M : ℝ) ^ 8 := by
    field_simp
  have hC : C8 ≤ 2 ^ 52 := by unfold C8; norm_num
  have hTT : (T : ℝ) ≤ (T : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · simp [h0]
    · have : (1 : ℝ) ≤ T := by exact_mod_cast hpos
      calc (T : ℝ) = (T : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (T : ℝ) ^ 4 := pow_le_pow_right₀ this (by norm_num)
  have hJ4 : (T : ℝ) * (M : ℝ) ^ 8 ≤ J ^ 4 := by
    have h1 : (T : ℝ) * (M : ℝ) ^ 2 ≤ J := by rw [hJ]; linarith
    calc (T : ℝ) * (M : ℝ) ^ 8 ≤ (T : ℝ) ^ 4 * (M : ℝ) ^ 8 := mul_le_mul_of_nonneg_right hTT (by positivity)
      _ = ((T : ℝ) * (M : ℝ) ^ 2) ^ 4 := by ring
      _ ≤ J ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  rw [hQ, hbN, hR, le_div_iff₀ (by positivity)]
  have hb0 : (0 : ℝ) ≤ b ^ 5 := by positivity
  calc C8 * (T : ℝ) * b ^ 5 * (M : ℝ) ^ 8 = C8 * b ^ 5 * ((T : ℝ) * (M : ℝ) ^ 8) := by ring
    _ ≤ 2 ^ 52 * a ^ 4 * J ^ 4 :=
        mul_le_mul (mul_le_mul hC h2 hb0 (by norm_num)) hJ4 (by positivity) (by positivity)
    _ = a ^ 4 * 2 ^ 52 * J ^ 4 := by ring

/-! ## The call samples -/

section Call
open NearCubicWires.WireExponent3_5.Cost
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

def callKh (P : StarParams) : ℕ := P.s * (P.r / 2)

theorem callN_eq (P : StarParams) : (P.b + 1) ^ (P.r / 2) = 2 ^ callKh P := by
  rw [P.b_succ, ← pow_mul]
  rfl

/-- **The indexing of the live halves**: `FinalPass.errorsEquiv`'s mixed-radix codes, as numbers below `2^{kh}`. -/
def callEqv (P : StarParams) : P.Errors ≃ Fin (2 ^ callKh P) := (errorsEquiv P).trans (finCongr (callN_eq P))

theorem bitR_and (x y : Bool) : bitR (x && y) = bitR x * bitR y := by cases x <;> cases y <;> simp [bitR]

theorem bitC_mul_eq (x y : Bool) : bitC x * bitC y = ((bitR (x && y) : ℝ) : ℂ) := by
  rw [bitR_and]; push_cast; rw [bitR_cast, bitR_cast]

section SymCall
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n)) (translation : List ℕ)

/-- The SYM matrix index `t = ((e, e'), τ)`: the final seeds and a joint state (row:matrix). -/
abbrev SymIndex : Type :=
  (GapSeed (I.filterParams .sym n) × (symListParams I n a Cs carriers).FlatSeed) × SymState (symM (I.starParams n hs) Cs)

def symStateBits (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (t : SymIndex I hs Cs carriers) (x : Cell (2 ^ callKh (I.starParams n hs))) : Bool :=
  maskBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers (I.filterParams .sym n)
      t.1.1 ((I.starParams n hs).point c.1 ((callEqv _).symm x.1) ((callEqv _).symm x.2)) &&
    symIndicator (symM (I.starParams n hs) Cs)
      (symRepFast (I.starParams n hs) Cs (symListParams I n a Cs carriers) t.1.2 c.1 ((callEqv _).symm x.1)
        ((callEqv _).symm x.2)) t.2

/-- `2𝔐 = 2·Π_j(m_j+1)²·Π_jP_j` (row:sampler-interface for SYM) as a natural number. -/
def symMassNat : ℕ :=
  2 * ((∏ j, (symM (I.starParams n hs) Cs j + 1) ^ 2) * ∏ j, symModulus (symM (I.starParams n hs) Cs j))

def symCount : ℕ :=
  sampleCount (callKh (I.starParams n hs)) I.D n (Fintype.card (SymIndex I hs Cs carriers) * symMassNat I hs Cs ^ 2 + 1)

/-- **The SYM call sample** (the computable `symS`): the greedy sample list of `samp:seed` at the call's own states. -/
def symCallSample : CallSample (I.starParams n hs) :=
  ⟨2 ^ callKh (I.starParams n hs), symCount I hs Cs carriers, callEqv _,
    greedySample (seedParamsFor (callKh (I.starParams n hs)) (symCount I hs Cs carriers))
      (symStateBits I hs Cs carriers translation)⟩

theorem symRep_eq_fast (P : StarParams) (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (Pl : FlatListParams)
    (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) : symRep P Cs Pl el c u v = symRepFast P Cs Pl el c u v := by
  unfold symRep symRepFast FlatListParams.jointState
  simp only [flatReport_eq_fast]

theorem symCallStates_eq (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (s : GapSeed (I.filterParams .sym n) × (symListParams I n a Cs carriers).FlatSeed)
    (τ : SymState (symM (I.starParams n hs) Cs)) :
    symCallStates I hs Cs carriers translation (symCallSample I hs Cs carriers translation) c s τ =
      fun u v => ((bitR (symStateBits I hs Cs carriers translation c (s, τ) (u, v)) : ℝ) : ℂ) := by
  funext u v
  unfold symCallStates symStateAt symStateMatrix stateMatrix symStateBits
  simp only [symMask_eq_maskBits, symRep_eq_fast, bitC_mul_eq]
  rfl

theorem starAt_pos (hs : I.StarAt n) : 0 < n := by
  have h2 : 4 * B.rOf n ≤ n := hs.2.2.1
  have h1 : 2 ≤ B.rOf n := hs.2.1
  omega

theorem symMassNat_pos : 1 ≤ symMassNat I hs Cs := by
  unfold symMassNat
  have h1 : 0 < ∏ j, (symM (I.starParams n hs) Cs j + 1) ^ 2 := Finset.prod_pos fun j _ => by positivity
  have h2 : 0 < ∏ j, symModulus (symM (I.starParams n hs) Cs j) :=
    Finset.prod_pos fun j _ => by unfold symModulus; omega
  have := Nat.mul_pos h1 h2
  omega

theorem symMassNat_cast : (symMassNat I hs Cs : ℝ) = 2 * symMass (I.starParams n hs) Cs := by
  unfold symMassNat symMass
  push_cast
  ring

/-- **The SYM call sample meets its target** (the `sym_good` field of `CallSampler`): `Q > 0` and the column-averaged
maximum state error is at most `n^{−D}/(2𝔐)`. -/
theorem symCallSample_good :
    0 < (symCallSample I hs Cs carriers translation).Q ∧
      ∃ ηz : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} → ℝ,
        (∀ c s τ, ‖sampleError (symCallStates I hs Cs carriers translation (symCallSample I hs Cs carriers translation)
            c s τ) (symCallSample I hs Cs carriers translation).S‖ /
            ((symCallSample I hs Cs carriers translation).Q * (symCallSample I hs Cs carriers translation).N) ≤ ηz c) ∧
        uMean ηz ≤ (n : ℝ) ^ (-(I.D : ℝ)) / (2 * symMass (I.starParams n hs) Cs) := by
  have hn : 1 ≤ n := starAt_pos I hs
  have hM := symMassNat_pos I hs Cs
  have hNQ : 2 ^ callKh (I.starParams n hs) ≤ symCount I hs Cs carriers :=
    N_le_sampleCount _ _ _ _ hn (by omega)
  refine ⟨lt_of_lt_of_le Nat.one_le_two_pow hNQ, ?_⟩
  have hη : (0 : ℝ) ≤ (n : ℝ) ^ (-(I.D : ℝ)) / (symMassNat I hs Cs : ℝ) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  obtain ⟨ηz, hz, hmean⟩ := greedySample_good (seedParamsFor (callKh (I.starParams n hs)) (symCount I hs Cs carriers))
    hNQ (symStateBits I hs Cs carriers translation) _ hη
    (sampleCount_mass_rate _ _ _ _ _ hn hM)
  refine ⟨ηz, fun c s τ => ?_, ?_⟩
  · rw [symCallStates_eq]
    exact hz c (s, τ)
  · rw [← symMassNat_cast]
    exact hmean

end SymCall

section ThrCall
variable (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- The THR matrix index `t = (e, g, p, s)`: the final seed, the equation, the prime and the residue (row:matrix). -/
abbrev ThrIndex : Type :=
  GapSeed (I.filterParams .thr n) × (ThrEq (I.starParams n hs) Cs algorithm ×
    Σ pr : PrimeIndex (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs)), ZMod pr.val)

def thrStateBits (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (t : ThrIndex algorithm I hs Cs) (x : Cell (2 ^ callKh (I.starParams n hs))) : Bool :=
  maskBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers (I.filterParams .thr n)
      t.1 ((I.starParams n hs).point c.1 ((callEqv _).symm x.1) ((callEqv _).symm x.2)) &&
    thrStates (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs algorithm
      (thrCallDen algorithm I hs Cs) (thrCallReportBits algorithm I hs Cs carriers translation) (callEqv _) c t.2.1
      t.2.2.1 t.2.2.2 x.1 x.2

/-- `2|𝒢|·cutoff + 1` (row:sampler-interface for THR, `𝔐 = |𝒢|·max_p p ≤ |𝒢|·cutoff`) as a natural number. -/
def thrMassNat : ℕ :=
  2 * Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) *
    thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) + 1

/-- **The THR sample count**: `samp:q` at `h = 4` for the call's `|T|` state matrices per column and the target
`n^{−D}/(2|𝒢|·cutoff + 1)`. -/
def thrCount : ℕ :=
  sampleCount (callKh (I.starParams n hs)) I.D n
    (Fintype.card (ThrIndex algorithm I hs Cs) * thrMassNat algorithm I hs Cs ^ 2 + 1)

/-- **The THR call sample** (the computable `thrS`): the greedy sample list of `samp:seed` at the call's own states. -/
def thrCallSample : CallSample (I.starParams n hs) :=
  ⟨2 ^ callKh (I.starParams n hs), thrCount algorithm I hs Cs, callEqv _,
    greedySample (seedParamsFor (callKh (I.starParams n hs)) (thrCount algorithm I hs Cs))
      (thrStateBits algorithm I hs Cs carriers translation)⟩

theorem thrCallStates_eq
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (e : GapSeed (I.filterParams .thr n)) (g : ThrEq (I.starParams n hs) Cs algorithm)
    (pr : PrimeIndex (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs))) (s : ZMod pr.val) :
    thrCallStates algorithm I hs Cs carriers translation (thrCallSample algorithm I hs Cs carriers translation)
        c e g pr s =
      fun u v => ((bitR (thrStateBits algorithm I hs Cs carriers translation c (e, g, ⟨pr, s⟩) (u, v)) : ℝ) : ℂ) := by
  funext u v
  unfold thrCallStates thrStateAt thrStateMatrix stateMatrix thrStateBits
  simp only [symMask_eq_maskBits, thrCallReport_eq_bits, bitC_mul_eq]
  rfl

/-- **The THR call sample meets its target** (the `thr_good` field of `CallSampler`): `Q > 0` and
`2|𝒢|·cutoff·E_z max ≤ n^{−D}`. -/
theorem thrCallSample_good :
    0 < (thrCallSample algorithm I hs Cs carriers translation).Q ∧
      ∃ ηz : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} → ℝ,
        (∀ c e g pr s, ‖sampleError
          (thrCallStates algorithm I hs Cs carriers translation (thrCallSample algorithm I hs Cs carriers translation)
            c e g pr s) (thrCallSample algorithm I hs Cs carriers translation).S‖ /
            ((thrCallSample algorithm I hs Cs carriers translation).Q *
              (thrCallSample algorithm I hs Cs carriers translation).N) ≤ ηz c) ∧
        2 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
          (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) * uMean ηz ≤
            (n : ℝ) ^ (-(I.D : ℝ)) := by
  have hn : 1 ≤ n := starAt_pos I hs
  have hM : 1 ≤ thrMassNat algorithm I hs Cs := by unfold thrMassNat; omega
  have hNQ : 2 ^ callKh (I.starParams n hs) ≤ thrCount algorithm I hs Cs :=
    N_le_sampleCount _ _ _ _ hn (by omega)
  refine ⟨lt_of_lt_of_le Nat.one_le_two_pow hNQ, ?_⟩
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(I.D : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hMr : (0 : ℝ) < (thrMassNat algorithm I hs Cs : ℝ) := by exact_mod_cast hM
  have hη : (0 : ℝ) ≤ (n : ℝ) ^ (-(I.D : ℝ)) / (thrMassNat algorithm I hs Cs : ℝ) := div_nonneg hx0 hMr.le
  obtain ⟨ηz, hz, hmean⟩ := greedySample_good (seedParamsFor (callKh (I.starParams n hs)) (thrCount algorithm I hs Cs))
    hNQ (thrStateBits algorithm I hs Cs carriers translation) _ hη
    (sampleCount_mass_rate _ _ _ _ _ hn hM)
  refine ⟨ηz, fun c e g pr s => ?_, ?_⟩
  · rw [thrCallStates_eq]
    exact hz c (e, g, ⟨pr, s⟩)
  · have hK : 2 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
        (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) + 1 =
          (thrMassNat algorithm I hs Cs : ℝ) := by
      unfold thrMassNat; push_cast; ring
    have hK0 : (0 : ℝ) ≤ 2 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
        (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) := by positivity
    generalize 2 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
        (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) = K at hK hK0 ⊢
    rw [← hK] at hmean hMr
    calc K * uMean ηz ≤ K * ((n : ℝ) ^ (-(I.D : ℝ)) / (K + 1)) := mul_le_mul_of_nonneg_left hmean hK0
      _ ≤ (n : ℝ) ^ (-(I.D : ℝ)) := by
          rw [mul_div_assoc', div_le_iff₀ hMr]
          nlinarith

end ThrCall

/-! ## The sampler -/

def greedySampler (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm) : CallSampler I algorithm where
  symS := fun Cs carriers translation hs => symCallSample I hs Cs carriers translation
  thrS := fun Cs carriers translation hs => thrCallSample algorithm I hs Cs carriers translation
  sym_good := fun Cs carriers translation hs => symCallSample_good I hs Cs carriers translation
  thr_good := fun Cs carriers translation hs => thrCallSample_good algorithm I hs Cs carriers translation

/-- **The primitive's printed value at the greedy sampler, computable** (C5's ref with C4's samples). -/
def greedyValue (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm) : PrimRequest → ℚ :=
  fusedValueBits I algorithm (greedySampler I algorithm)

theorem greedyValue_error (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) (hfe : I.D + 2 ≤ I.filterErrDeg)
    (hG : ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
      (translation : List ℕ), I.Call (thrReq n a ha Cs carriers translation) → ∀ hs : I.StarAt n,
        (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
          (n : ℝ) ^ (-(I.D : ℝ)) / 8)
    (req : PrimRequest) (h : I.Call req) :
    |((greedyValue I algorithm req : ℚ) : ℝ) - I.truth req| ≤ (req.n : ℝ) ^ (-(I.D : ℝ)) :=
  fusedValueBits_error spectrum theta algorithm I (greedySampler I algorithm) hfe hG req h

end Call

end NearCubicWires.WireExponent3_5.SeedFix

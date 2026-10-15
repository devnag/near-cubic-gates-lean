import Proof.Amplification.XorResourcesArithmetic
import Proof.Circuits.ValidatorLeafWidthCore

/-! Reduced rational coefficient widths for the exact CLW sampled form. -/
namespace NearCubicWires.RepairXor
open SourceInterfaces ExecutableInterfaces RepairRepresentation ValidatorLeafWidthCore
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem radius_parameters (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2) :
    1 ≤ delta.num.natAbs ∧ 2 * delta.num.natAbs < delta.den ∧
      delta = (delta.num.natAbs : ℚ) / delta.den := by
  have hp : 0 < delta.num := Rat.num_pos.mpr hd
  have ha : (delta.num.natAbs : ℤ) = delta.num := Int.natAbs_of_nonneg hp.le
  have he : delta = (delta.num.natAbs : ℚ) / delta.den := by
    calc
      delta = (delta.num : ℚ) / delta.den := delta.num_div_den.symm
      _ = _ := by
        have hcast := congrArg (fun z : ℤ => (z : ℚ)) ha
        simp only [Int.cast_natCast] at hcast
        exact congrArg (fun z : ℚ => z / delta.den) hcast.symm
  have habs : 1 ≤ delta.num.natAbs := by
    have hi : (1 : ℤ) ≤ (delta.num.natAbs : ℤ) := by omega
    exact_mod_cast hi
  have hb : (0 : ℚ) < delta.den := by exact_mod_cast delta.pos
  have hdiv : (delta.num.natAbs : ℚ) / delta.den < 1 / 2 := he ▸ hh
  have hlt : (2 : ℚ) * delta.num.natAbs < delta.den := by
    have hm := (div_lt_iff₀ hb).mp hdiv
    linarith
  exact ⟨habs, by exact_mod_cast hlt, he⟩

theorem epsilon_denominator_lower (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {j : ℕ} (hj : 1 ≤ j) :
    (1 : ℝ) / delta.den ≤ (delta : ℝ) ∧
      1 / (2 * (delta.den : ℝ) ^ j) ≤ xorEpsilon (delta : ℝ) j := by
  obtain ⟨ha, hab, he⟩ := radius_parameters delta hd hh
  have hb : (0 : ℝ) < delta.den := by exact_mod_cast delta.pos
  have hq : delta * (delta.den : ℚ) = delta.num.natAbs := by
    calc
      _ = ((delta.num.natAbs : ℚ) / delta.den) * delta.den :=
        congrArg (fun z : ℚ => z * delta.den) he
      _ = _ := div_mul_cancel₀ _ (by exact_mod_cast delta.pos.ne')
  have hmul : (delta : ℝ) * delta.den = delta.num.natAbs := by exact_mod_cast hq
  have har : (1 : ℝ) ≤ delta.num.natAbs := by exact_mod_cast ha
  have hbar : (2 : ℝ) * delta.num.natAbs + 1 ≤ delta.den := by exact_mod_cast hab
  have hone : (1 : ℝ) / delta.den ≤ (delta : ℝ) := by
    apply (div_le_iff₀ hb).2
    linarith
  have hfirst : (1 : ℝ) / delta.den ≤ 1 - (delta : ℝ) := by
    apply (div_le_iff₀ hb).2
    nlinarith
  have hlast : (1 : ℝ) / (2 * delta.den) ≤ 1 / 2 - (delta : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hbase : 0 ≤ 1 - (delta : ℝ) := (by positivity : (0 : ℝ) ≤ 1 / delta.den).trans hfirst
  refine ⟨hone, ?_⟩
  have hj' : j - 1 + 1 = j := by omega
  calc
    _ = ((1 : ℝ) / delta.den) ^ (j - 1) * (1 / (2 * delta.den)) := by
      conv_lhs => rw [← hj', pow_succ]
      simp only [one_div_pow]
      field_simp
    _ ≤ (1 - (delta : ℝ)) ^ (j - 1) * (1 / 2 - (delta : ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hfirst _) hlast
        (by positivity) (pow_nonneg hbase _)
    _ = _ := rfl

theorem sampleCount_integer_bound (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    (n j : ℕ) (hj : 1 ≤ j) :
    sampleCount delta n j ≤ 16 * (n + 1) * delta.den ^ (2 * j + 2) := by
  obtain ⟨hdelta, heps⟩ := epsilon_denominator_lower delta hd hh hj
  have hb : (0 : ℝ) < delta.den := by exact_mod_cast delta.pos
  have hden : ((1 : ℝ) / delta.den) ^ 2 * (1 / (2 * (delta.den : ℝ) ^ j)) ^ 2 ≤
      (delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hdelta 2)
      (pow_le_pow_left₀ (by positivity) heps 2) (by positivity) (by positivity)
  unfold sampleCount
  apply Nat.ceil_le.mpr
  push_cast
  calc
    _ ≤ 4 * ((n : ℝ) + 1) /
        (((1 : ℝ) / delta.den) ^ 2 * (1 / (2 * (delta.den : ℝ) ^ j)) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 16 * ((n : ℝ) + 1) * (delta.den : ℝ) ^ (2 * j + 2) := by
      rw [pow_add, Nat.mul_comm 2 j, pow_mul]
      field_simp
      ring

theorem fraction_reduction_bounds (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (((num : ℚ) / den).num.natAbs ≤ num.natAbs) ∧
      ((num : ℚ) / den).den ≤ den := by
  have hdz : (den : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨c, hn, hden⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den num hdz
  have hn' := congrArg Int.natAbs hn
  have hd' := congrArg Int.natAbs hden
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn' hd'
  have hc : 0 < c.natAbs := by
    by_contra h
    have hz : c.natAbs = 0 := by omega
    rw [hz, zero_mul] at hd'
    omega
  constructor
  · exact (Nat.le_mul_of_pos_left _ hc).trans_eq hn'.symm
  · exact (Nat.le_mul_of_pos_left _ hc).trans_eq hd'.symm

def rawNumerator (b j : ℕ) : ℕ := 2 * b ^ j
def rawDenominator (a b j : ℕ) : ℕ :=
  (2 * b + a) * (b - a) ^ (j - 2) * (b - 2 * a)

theorem raw_denominator_bounds (a b j : ℕ) (ha : 1 ≤ a) (hab : 2 * a < b)
    (hj : 2 ≤ j) :
    0 < rawDenominator a b j ∧ rawDenominator a b j ≤ rawNumerator b j := by
  have hb : 0 < b := by omega
  have hba : 0 < b - a := by omega
  have hbaa : 0 < b - 2 * a := by omega
  have hsub : b - 2 * a + 2 * a = b := Nat.sub_add_cancel (by omega)
  have hprod : (2 * b + a) * (b - 2 * a) ≤ 2 * b ^ 2 := by nlinarith
  have hj' : j - 2 + 2 = j := by omega
  constructor
  · unfold rawDenominator; positivity
  · unfold rawDenominator rawNumerator
    calc
      _ = ((2 * b + a) * (b - 2 * a)) * (b - a) ^ (j - 2) := by ring
      _ ≤ (2 * b ^ 2) * b ^ (j - 2) :=
        Nat.mul_le_mul hprod (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
      _ = 2 * b ^ j := by
        conv_rhs => rw [← hj', pow_add]
        ring

theorem alpha_closed_form (a b : ℚ) (t : ℕ)
    (hb : b ≠ 0) (hba : b - a ≠ 0) (hb2a : b - 2 * a ≠ 0)
    (h2ba : 2 * b + a ≠ 0) :
    alphaQ (a / b) (t + 2) =
      2 * b ^ (t + 2) / ((2 * b + a) * (b - a) ^ t * (b - 2 * a)) := by
  have hsub : 1 - a / b = (b - a) / b := by field_simp
  have hhalf : 1 / 2 - a / b = (b - 2 * a) / (2 * b) := by field_simp
  have hadd : 2 + a / b = (2 * b + a) / b := by field_simp
  have hi : t + 2 - 1 = t + 1 := by omega
  simp only [alphaQ, epsilonQ, hi, hsub, hhalf, hadd, div_pow, pow_succ]
  field_simp

theorem alpha_raw (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    (j : ℕ) (hj : 2 ≤ j) :
    alphaQ delta j = (rawNumerator delta.den j : ℚ) /
      rawDenominator delta.num.natAbs delta.den j := by
  obtain ⟨ha, hab, he⟩ := radius_parameters delta hd hh
  have hb : (0 : ℚ) < delta.den := by exact_mod_cast delta.pos
  have habQ : (2 : ℚ) * delta.num.natAbs < delta.den := by exact_mod_cast hab
  have haQ : (1 : ℚ) ≤ delta.num.natAbs := by exact_mod_cast ha
  have hba : delta.num.natAbs ≤ delta.den := by omega
  have h2ba : 2 * delta.num.natAbs ≤ delta.den := by omega
  have hj' : j - 2 + 2 = j := by omega
  calc
    alphaQ delta j = alphaQ ((delta.num.natAbs : ℚ) / delta.den) j :=
      congrArg (fun z : ℚ => alphaQ z j) he
    _ = alphaQ ((delta.num.natAbs : ℚ) / delta.den) (j - 2 + 2) := by rw [hj']
    _ = 2 * (delta.den : ℚ) ^ (j - 2 + 2) /
        ((2 * delta.den + delta.num.natAbs) * (delta.den - delta.num.natAbs) ^ (j - 2) *
          (delta.den - 2 * delta.num.natAbs)) :=
      alpha_closed_form _ _ _ (ne_of_gt hb) (by linarith) (by linarith) (by linarith)
    _ = _ := by
      rw [hj']
      simp only [rawNumerator, rawDenominator, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hba, Nat.cast_sub h2ba]

theorem common_envelope_bits (b n k : ℕ) :
    natBitLength (32 * (n + 1) * b ^ (3 * k + 2)) ≤
      (8 + 5 * natBitLength b) * (n + k + 1) := by
  have hsmall (v : ℕ) : v ≤ 2 ^ natBitLength v :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two v).le
  have hbound : 32 * (n + 1) * b ^ (3 * k + 2) ≤
      2 ^ (5 + natBitLength (n + 1) + (3 * k + 2) * natBitLength b) := by
    calc
      _ ≤ 2 ^ 5 * 2 ^ natBitLength (n + 1) * (2 ^ natBitLength b) ^ (3 * k + 2) := by
        norm_num only [Nat.reducePow]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (hsmall _))
          (Nat.pow_le_pow_left (hsmall _) _)
      _ = _ := by rw [← pow_add, ← pow_mul, ← pow_add]; congr 1; ring
  have hbits := natBitLength_mono hbound
  have hlog : natBitLength (n + 1) ≤ n + 2 := by
    unfold natBitLength
    have := Nat.log_le_self 2 (n + 1)
    omega
  have hbpos : 1 ≤ natBitLength b := by unfold natBitLength; omega
  have hpow (x : ℕ) : natBitLength (2 ^ x) = x + 1 := by
    simp [natBitLength, Nat.log_pow]
  rw [hpow] at hbits
  nlinarith

theorem affine_coefficient_magnitudes (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    (n j : ℕ) (hj : 2 ≤ j) :
    let B := 32 * (n + 1) * delta.den ^ (3 * j + 2)
    let sample := alphaQ delta j / sampleCount delta n j
    let constant := (1 - alphaQ delta j) / 2
    (sample.num.natAbs ≤ B ∧ sample.den ≤ B) ∧
      (constant.num.natAbs ≤ B ∧ constant.den ≤ B) := by
  obtain ⟨ha, hab, _⟩ := radius_parameters delta hd hh
  obtain ⟨hD, hDN⟩ := raw_denominator_bounds delta.num.natAbs delta.den j ha hab hj
  let N := rawNumerator delta.den j
  let D := rawDenominator delta.num.natAbs delta.den j
  let ell := sampleCount delta n j
  let B := 32 * (n + 1) * delta.den ^ (3 * j + 2)
  change ((alphaQ delta j / ell).num.natAbs ≤ B ∧ (alphaQ delta j / ell).den ≤ B) ∧
    ((1 - alphaQ delta j) / 2).num.natAbs ≤ B ∧ ((1 - alphaQ delta j) / 2).den ≤ B
  have hEll : 0 < ell := sampleCount_positive delta hd hh n j
  have hEllBound : ell ≤ 16 * (n + 1) * delta.den ^ (2 * j + 2) :=
    sampleCount_integer_bound delta hd hh n j (by omega)
  have hscale : N * (16 * (n + 1) * delta.den ^ (2 * j + 2)) = B := by
    dsimp [N, rawNumerator, B]
    calc
      _ = 32 * (n + 1) * (delta.den ^ j * delta.den ^ (2 * j + 2)) := by ring
      _ = _ := by rw [← pow_add, show j + (2 * j + 2) = 3 * j + 2 by omega]
  have hDBound : D * ell ≤ B :=
    (Nat.mul_le_mul hDN hEllBound).trans_eq hscale
  have hpow : 1 ≤ delta.den ^ (2 * j + 2) := by
    have := pow_pos delta.pos (2 * j + 2)
    omega
  have hfactor : 4 ≤ 32 * (n + 1) * delta.den ^ (2 * j + 2) := by nlinarith
  have hFour : 4 * delta.den ^ j ≤ B := by
    calc
      _ ≤ (32 * (n + 1) * delta.den ^ (2 * j + 2)) * delta.den ^ j :=
        Nat.mul_le_mul_right _ hfactor
      _ = B := by
        dsimp [B]
        rw [Nat.mul_assoc, ← pow_add, show 2 * j + 2 + j = 3 * j + 2 by omega]
  have hNBound : N ≤ B := by
    have hsmall : N ≤ 4 * delta.den ^ j := by dsimp [N, rawNumerator]; omega
    exact hsmall.trans hFour
  have hTwoN : 2 * N ≤ B := by
    simpa only [N, rawNumerator, ← Nat.mul_assoc, Nat.reduceMul] using hFour
  have hsample : alphaQ delta j / ell = ((N : ℤ) : ℚ) / ((D * ell : ℕ) : ℚ) := by
    rw [alpha_raw delta hd hh j hj]
    simp only [N, D, Int.cast_natCast, Nat.cast_mul, div_div]
  have hconstant : (1 - alphaQ delta j) / 2 =
      (((D : ℤ) - (N : ℤ) : ℤ) : ℚ) / ((2 * D : ℕ) : ℚ) := by
    rw [alpha_raw delta hd hh j hj]
    change (1 - (N : ℚ) / D) / 2 = _
    push_cast
    have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast (show 0 < D from hD).ne'
    field_simp
  have hs := fraction_reduction_bounds (N : ℤ) (D * ell) (Nat.mul_pos hD hEll)
  rw [← hsample] at hs
  simp only [Int.natAbs_natCast] at hs
  have hc := fraction_reduction_bounds ((D : ℤ) - (N : ℤ)) (2 * D) (by omega)
  rw [← hconstant] at hc
  have hnum : ((D : ℤ) - (N : ℤ)).natAbs ≤ B := by
    have h := Int.natAbs_sub_le (D : ℤ) (N : ℤ)
    simp only [Int.natAbs_natCast] at h
    exact h.trans ((show D + N ≤ 2 * N by omega).trans hTwoN)
  exact ⟨⟨hs.1.trans hNBound, hs.2.trans hDBound⟩,
    hc.1.trans hnum, hc.2.trans ((Nat.mul_le_mul_left 2 hDN).trans hTwoN)⟩

theorem affine_coefficient_bits (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    (n j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    let sample := alphaQ delta j / sampleCount delta n j
    let constant := (1 - alphaQ delta j) / 2
    (natBitLength sample.num.natAbs ≤ xorBits delta n k ∧
      natBitLength sample.den ≤ xorBits delta n k) ∧
    (natBitLength constant.num.natAbs ≤ xorBits delta n k ∧
      natBitLength constant.den ≤ xorBits delta n k) := by
  obtain ⟨⟨hsn, hsd⟩, hcn, hcd⟩ := affine_coefficient_magnitudes delta hd hh n j hj
  have hb : 32 * (n + 1) * delta.den ^ (3 * j + 2) ≤
      32 * (n + 1) * delta.den ^ (3 * k + 2) := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right delta.pos (by omega)
  have width (v : ℕ) (hv : v ≤ 32 * (n + 1) * delta.den ^ (3 * j + 2)) :
      natBitLength v ≤ xorBits delta n k :=
    (natBitLength_mono (hv.trans hb)).trans (common_envelope_bits delta.den n k)
  exact ⟨⟨width _ hsn, width _ hsd⟩, width _ hcn, width _ hcd⟩

end NearCubicWires.RepairXor

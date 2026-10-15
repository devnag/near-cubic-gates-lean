import Proof.Wire_3_5.TransferCompleteness

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer

section Params

theorem sqrt_24v0_le (ε : ℚ) (hε0 : 0 < ε) : Real.sqrt (24 * (((ε ^ 2 / 10000 : ℚ)) : ℝ)) ≤ (ε : ℝ) / 20 := by
  have hε : (0 : ℝ) ≤ ε := by exact_mod_cast hε0.le
  rw [show (24 : ℝ) * ((ε ^ 2 / 10000 : ℚ) : ℝ) = 24 / 10000 * (ε : ℝ) ^ 2 by push_cast; ring]
  calc Real.sqrt (24 / 10000 * (ε : ℝ) ^ 2) ≤ Real.sqrt (((ε : ℝ) / 20) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = (ε : ℝ) / 20 := Real.sqrt_sq (by positivity)

/-- The soundness constants: `v₀ = ε²/10⁴`, `ε₀ = v₀/2`, outer error `ε/6`, threshold `τ`. -/
noncomputable def unionSoundParams {cp sp : ℝ} (hsp : 0 ≤ sp) (ε : ℚ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεg : (ε : ℝ) ≤ (cp - sp) / 1000) (τ : ℚ) (hτ1 : (cp + sp) / 2 ≤ (τ : ℝ)) :
    MaskedSoundnessParameters cp sp where
  v0 := ε ^ 2 / 10000
  eps0 := ε ^ 2 / 20000
  outerError := ε / 6
  threshold := τ
  v0_pos := by positivity
  v0_le := by nlinarith
  eps0_nonneg := by positivity
  eps0_le_v0 := by nlinarith
  sp_nonneg := hsp
  thresholdAboveMidpoint := hτ1
  roundingReserve := by
    have hs := sqrt_24v0_le ε hε0
    have hε : (0 : ℝ) < ε := by exact_mod_cast hε0
    have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
    push_cast at hs ⊢
    nlinarith
  outerReserve := by
    have hε : (0 : ℝ) < ε := by exact_mod_cast hε0
    push_cast
    linarith

theorem sqrt_zeta_eq (ε : ℚ) : Real.sqrt ((((ε ^ 2 / 10000) / 10) ^ 2 : ℚ) : ℝ) = (ε : ℝ) ^ 2 / 100000 := by
  rw [show ((((ε ^ 2 / 10000) / 10) ^ 2 : ℚ) : ℝ) = ((ε : ℝ) ^ 2 / 100000) ^ 2 by push_cast; ring]
  exact Real.sqrt_sq (by positivity)

/-- The completeness constants: `ζ = (v₀/10)²`, `δ = v₀/100`, `β = ξ = ε/100`. -/
noncomputable def unionCompleteParams {cp sp : ℝ} (hsp : 0 ≤ sp) (ε : ℚ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεg : (ε : ℝ) ≤ (cp - sp) / 1000) (τ : ℚ) (hτ1 : (cp + sp) / 2 ≤ (τ : ℝ))
    (hτ2 : (τ : ℝ) ≤ (cp + sp) / 2 + (cp - sp) / 10) :
    MaskedCompletenessParameters (unionSoundParams hsp ε hε0 hε1 hεg τ hτ1) where
  ζ := ((ε ^ 2 / 10000) / 10) ^ 2
  δ := (ε ^ 2 / 10000) / 100
  β := ε / 100
  ξ := ε / 100
  ζ_nonneg := by positivity
  δ_nonneg := by positivity
  β_nonneg := by positivity
  ξ_nonneg := by positivity
  ζ_le_one := by nlinarith [pow_le_one₀ hε0.le hε1 (n := 2)]
  δ_le_one := by nlinarith [pow_le_one₀ hε0.le hε1 (n := 2)]
  V_slack := by
    rw [sqrt_zeta_eq]
    simp only [unionSoundParams]
    have hε : (0 : ℝ) < ε := by exact_mod_cast hε0
    have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
    push_cast
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (ε : ℝ) ^ 2 := ⟨_, rfl⟩
    rw [← hx]
    have hx0 : 0 < x := by rw [hx]; positivity
    have hx1 : x ≤ 1 := by rw [hx]; nlinarith
    have ha : x / 100000 + x / 10000 / 100 + (x / 10000 / 100) ^ 2 ≤ 2 * x / 100000 := by nlinarith
    have ha0 : 0 ≤ x / 100000 + x / 10000 / 100 + (x / 10000 / 100) ^ 2 := by positivity
    have hsq : (x / 100000 + x / 10000 / 100 + (x / 10000 / 100) ^ 2) ^ 2 ≤ (2 * x / 100000) ^ 2 :=
      pow_le_pow_left₀ ha0 ha 2
    nlinarith
  Q_slack := by
    simp only [unionSoundParams]
    have hε : (0 : ℝ) < ε := by exact_mod_cast hε0
    have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
    have h2 : (ε : ℝ) ^ 2 ≤ 1 := by nlinarith
    push_cast
    nlinarith [sq_nonneg ((ε : ℝ) ^ 2)]
  μ_slack := by
    rw [sqrt_zeta_eq]
    simp only [unionSoundParams]
    have hε : (0 : ℝ) < ε := by exact_mod_cast hε0
    have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
    have h2 : (ε : ℝ) ^ 2 ≤ ε := by nlinarith
    push_cast
    nlinarith

end Params

/-- **Every PCPP gap has the masked verifier's constants** (soundness and completeness). -/
theorem exists_unionParams {cp sp : ℝ} (hsp : 0 ≤ sp) (hgap : sp < cp) :
    ∃ params : MaskedSoundnessParameters cp sp, Nonempty (MaskedCompletenessParameters params) := by
  have hg : 0 < cp - sp := by linarith
  obtain ⟨ε, hε0, hε⟩ := exists_rat_btwn (show (0 : ℝ) < min 1 ((cp - sp) / 1000) by positivity)
  obtain ⟨τ, hτ1, hτ2⟩ := exists_rat_btwn (show (cp + sp) / 2 < (cp + sp) / 2 + (cp - sp) / 10 by linarith)
  have hε0' : (0 : ℚ) < ε := by exact_mod_cast hε0
  have hε1 : ε ≤ 1 := by have := lt_of_lt_of_le hε (min_le_left _ _); exact_mod_cast this.le
  have hεg : (ε : ℝ) ≤ (cp - sp) / 1000 := (lt_of_lt_of_le hε (min_le_right _ _)).le
  exact ⟨unionSoundParams hsp ε hε0' hε1 hεg τ hτ1.le,
    ⟨unionCompleteParams hsp ε hε0' hε1 hεg τ hτ1.le hτ2.le⟩⟩

end NearCubicWires.WireExponent3_5.Transfer

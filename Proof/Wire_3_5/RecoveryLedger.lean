import Proof.Wire_3_5.RecoverySlice
import Proof.Wire_3_5.RecoveryLanguage

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open Filter Topology

section Grid
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

theorem epsilonQ_eq_eps (t : ℕ) : RepairRepresentation.epsilonQ ζ t = eps ζ t := rfl

/-- **The XOR sum's mass fits the grid**: `1/e_{t+1} ≤ ⌈2/e_t⌉ = Λ̄(q)` at `t = t(q)`. -/
theorem massCap_le_lambda (q : ℕ) :
    massCap ζ (rowBt h0 h1 q + 1) ≤ (rowBLambda h0 h1 2 q : ℚ) := by
  have ht : 1 ≤ rowBt h0 h1 q := (sched_spec h0 h1 (Lq q)).1
  have he := eps_pos h0 h1 (rowBt h0 h1 q)
  have hsucc := eps_succ (ζ := ζ) (rowBt h0 h1 q) ht
  unfold massCap rowBLambda
  rw [epsilonQ_eq_eps, hsucc]
  have hz : (1 : ℚ) / 2 ≤ 1 - ζ := by linarith
  have hce := Nat.le_ceil ((2 : ℚ) / eps ζ (rowBt h0 h1 q))
  refine le_trans ?_ hce
  rw [div_le_div_iff₀ (by positivity) he]
  nlinarith

theorem sqrt_div_sq (C L : ℕ) (hC : 1 ≤ C) : Nat.sqrt (C * L ^ 2 / C) = L := by
  rw [Nat.mul_div_cancel_left _ (by omega), sq, Nat.sqrt_eq]

/-- With the gate's grid `s = C_δΛ̄²`, the setup's mass is `Λ̄`. -/
theorem gridMassOf_rowB (Cδ : ℕ) (hC : 1 ≤ Cδ) (q : ℕ) :
    gridMassOf Cδ (rowBSparse h0 h1 2 Cδ) q = (rowBLambda h0 h1 2 q : ℚ) := by
  unfold gridMassOf rowBSparse
  rw [sqrt_div_sq _ _ hC]

theorem massCap_le_gridMass (Cδ : ℕ) (hC : 1 ≤ Cδ) (q : ℕ) :
    ((massCap ζ (rowBt h0 h1 q + 1) : ℚ) : ℝ) ≤ ((gridMassOf Cδ (rowBSparse h0 h1 2 Cδ) q : ℚ) : ℝ) := by
  rw [gridMassOf_rowB h0 h1 Cδ hC q]
  exact_mod_cast massCap_le_lambda h0 h1 q

theorem one_le_lambda (q : ℕ) : 1 ≤ rowBLambda h0 h1 2 q := by
  have he := eps_pos h0 h1 (rowBt h0 h1 q)
  have hle : eps ζ (rowBt h0 h1 q) ≤ 1 := by
    unfold eps
    have h2 : (1 - ζ) ^ (rowBt h0 h1 q - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith [pow_nonneg (show (0 : ℚ) ≤ 1 - ζ by linarith) (rowBt h0 h1 q - 1)]
  unfold rowBLambda
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  rw [Nat.ceil_eq_zero] at h
  have : (0 : ℚ) < 2 / eps ζ (rowBt h0 h1 q) := by positivity
  linarith

theorem one_le_gridMass (Cδ : ℕ) (hC : 1 ≤ Cδ) (q : ℕ) :
    1 ≤ ((gridMassOf Cδ (rowBSparse h0 h1 2 Cδ) q : ℚ) : ℝ) := by
  rw [gridMassOf_rowB h0 h1 Cδ hC q]
  exact_mod_cast one_le_lambda h0 h1 q

theorem one_le_gridSize (Cδ : ℕ) (hC : 1 ≤ Cδ) (q : ℕ) : 1 ≤ rowBSparse h0 h1 2 Cδ q := by
  unfold rowBSparse
  have := one_le_lambda h0 h1 q
  nlinarith

end Grid

section Errors

/-- **The filters' endpoint error** is eventually below `ξ > 0`: `2^{−errExp} ≤ 1/(q+2)` for `errExp ≥ clog(q+2)`. -/
theorem eventually_hξ (e : ℕ) (he : 1 ≤ e) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ q : ℕ in atTop, 1 / (2 : ℝ) ^ (e * Nat.clog 2 (q + 2)) ≤ ξ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ξ)
  filter_upwards [eventually_ge_atTop M] with q hq
  have h1 : ((q + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (e * Nat.clog 2 (q + 2)) := by
    have hc : q + 2 ≤ 2 ^ Nat.clog 2 (q + 2) := Nat.le_pow_clog (by norm_num) _
    have hm : 2 ^ Nat.clog 2 (q + 2) ≤ 2 ^ (e * Nat.clog 2 (q + 2)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ he)
    exact_mod_cast hc.trans hm
  have h2 : (1 / ξ) < ((q + 2 : ℕ) : ℝ) := by
    have : (M : ℝ) ≤ q := by exact_mod_cast hq
    push_cast; linarith
  have hpos : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by positivity
  calc 1 / (2 : ℝ) ^ (e * Nat.clog 2 (q + 2)) ≤ 1 / ((q + 2 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hpos h1
    _ ≤ ξ := by
      rw [div_le_iff₀ hpos]
      rw [div_lt_iff₀ hξ] at h2
      linarith

theorem eventually_hD {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (D : ℕ) (hD : 1 ≤ D) (eps0 : ℝ) (he : 0 < eps0) :
    ∀ᶠ q : ℕ in atTop, (1 + (rowBLambda h0 h1 2 q : ℝ)) ^ 4 * (q : ℝ) ^ (-(D : ℝ)) ≤ eps0 := by
  obtain ⟨K, hK⟩ := rowBLambda_pow16_le h0 h1 2
  obtain ⟨C, hC⟩ := exists_nat_gt (16 * (K : ℝ) / eps0)
  filter_upwards [eventually_mul_Lq_pow_le C 3, eventually_ge_atTop 1] with q hq hq1
  set Λ := rowBLambda h0 h1 2 q with hΛdef
  have hΛ1 : 1 ≤ Λ := one_le_lambda h0 h1 q
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  -- `(1+Λ)⁴ ≤ 16Λ⁴ ≤ 16Λ¹⁶ ≤ 16 K L³`
  have hΛr : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ1
  have h4 : (1 + (Λ : ℝ)) ^ 4 ≤ 16 * (Λ : ℝ) ^ 16 := by
    have ha : (1 + (Λ : ℝ)) ^ 4 ≤ (2 * Λ) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hb : (Λ : ℝ) ^ 4 ≤ (Λ : ℝ) ^ 16 := pow_le_pow_right₀ hΛr (by norm_num)
    nlinarith
  have hK' : (Λ : ℝ) ^ 16 ≤ K * (Lq q : ℝ) ^ 3 := by exact_mod_cast hK q
  have hq' : (C : ℝ) * (Lq q : ℝ) ^ 3 ≤ q := by exact_mod_cast hq
  have hL0 : (0 : ℝ) ≤ (Lq q : ℝ) ^ 3 := by positivity
  have hqD : (q : ℝ) ≤ (q : ℝ) ^ (D : ℝ) := by
    have : (q : ℝ) ^ (1 : ℝ) ≤ (q : ℝ) ^ (D : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1) (by exact_mod_cast hD)
    simpa using this
  have hpow : (q : ℝ) ^ (-(D : ℝ)) = 1 / (q : ℝ) ^ (D : ℝ) := by
    rw [Real.rpow_neg hqpos.le, one_div]
  have hqDpos : (0 : ℝ) < (q : ℝ) ^ (D : ℝ) := Real.rpow_pos_of_pos hqpos _
  rw [hpow, mul_one_div, div_le_iff₀ hqDpos]
  -- `16 K L³ ≤ ε₀ C L³ ≤ ε₀ q ≤ ε₀ q^D`
  have hCε : 16 * (K : ℝ) ≤ eps0 * C := by
    rw [div_lt_iff₀ he] at hC; linarith
  calc (1 + (Λ : ℝ)) ^ 4 ≤ 16 * (K * (Lq q : ℝ) ^ 3) := by nlinarith
    _ = (16 * (K : ℝ)) * (Lq q : ℝ) ^ 3 := by ring
    _ ≤ (eps0 * C) * (Lq q : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hCε hL0
    _ = eps0 * (C * (Lq q : ℝ) ^ 3) := by ring
    _ ≤ eps0 * q := mul_le_mul_of_nonneg_left hq' he.le
    _ ≤ eps0 * (q : ℝ) ^ (D : ℝ) := mul_le_mul_of_nonneg_left hqD he.le

end Errors

section Star

theorem eventually_star (cr : ℕ) (hcr : 1 ≤ cr) (kDeg : ℕ) (hk : 2 ≤ kDeg) :
    ∀ᶠ q : ℕ in atTop, Even (rowBr cr q) ∧ 2 ≤ rowBr cr q ∧ 4 * rowBr cr q ≤ q ∧
      Lq q ≤ starWidth (rowBr cr q) q ∧ starWidth (rowBr cr q) q ≤ Lq q ^ kDeg := by
  -- `r + 1 ≤ L` eventually, `8(1+c_r)L ≤ q` eventually, and `8(2μ+1) ≤ 2^μ` at `μ = L/2`
  have hμ : ∀ᶠ q : ℕ in atTop, 8 * (2 * (Lq q / 2) + 1) ^ 1 ≤ 2 ^ (Lq q / 2) := by
    have hT : Tendsto (fun q => Lq q / 2) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => by
        obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 tendsto_Lq (2 * b)
        exact ⟨N, fun q hq => by have := hN q hq; omega⟩
    exact hT.eventually (eventually_mul_affine_pow_le_two_pow 8 2 1 1)
  have hL2 : ∀ᶠ q : ℕ in atTop, 4 ≤ Lq q := tendsto_Lq.eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_rowBr_pow_le cr 1, eventually_mul_Lq_pow_le (8 * (1 + cr)) 1, hμ, hL2] with q hr hq8 hm hL4
  have hr2 : 2 ≤ rowBr cr q := two_le_rowBr hcr q
  have hrL : rowBr cr q + 1 ≤ Lq q := by
    have h1 : (rowBr cr q + 1) ^ 2 ≤ (rowBr cr q + 1) ^ 176 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : (rowBr cr q + 1) ^ 2 ≤ Lq q ^ 2 := by linarith
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2
  have h4r : 4 * rowBr cr q ≤ q := by
    have hlog : Nat.log 2 (Lq q) ≤ Lq q := Nat.log_le_self 2 (Lq q)
    have hrc : rowBr cr q ≤ 2 * (Lq q + cr) := by unfold rowBr; omega
    rw [pow_one] at hq8
    have hL1 := Lq_pos q
    nlinarith
  refine ⟨rowBr_even cr q, hr2, h4r, ?_, ?_⟩
  · -- `2^{L/2+1}·r ≤ q`, so `⌊log₂(q/r+1)⌋ ≥ L/2+1` and `k ≥ 2(L/2+1) ≥ L`
    have hq1 : 2 ^ (Lq q - 2) ≤ q := by
      have h := two_pow_pred_Lq_lt q
      have e : 2 ^ (Lq q - 2) * 2 = 2 ^ (Lq q - 1) := by
        rw [← pow_succ]; congr 1; omega
      have h2 : 1 ≤ 2 ^ (Lq q - 2) := Nat.one_le_two_pow
      omega
    have hm' : 8 * (2 * (Lq q / 2) + 1) ≤ 2 ^ (Lq q / 2) := by simpa using hm
    have e1 : 2 ^ (2 * (Lq q / 2) - 2) * 4 = 2 ^ (Lq q / 2) * 2 ^ (Lq q / 2) := by
      rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have e2 : 2 ^ (Lq q / 2 + 1) = 2 * 2 ^ (Lq q / 2) := by rw [pow_succ]; ring
    have h8 : 2 ^ (Lq q / 2 + 1) * (2 * (Lq q / 2) + 1) * 4 ≤ 2 ^ (2 * (Lq q / 2) - 2) * 4 := by
      rw [e1, e2]
      calc 2 * 2 ^ (Lq q / 2) * (2 * (Lq q / 2) + 1) * 4 = 2 ^ (Lq q / 2) * (8 * (2 * (Lq q / 2) + 1)) := by ring
        _ ≤ 2 ^ (Lq q / 2) * 2 ^ (Lq q / 2) := Nat.mul_le_mul_left _ hm'
    have h2 : 2 ^ (Lq q / 2 + 1) * (2 * (Lq q / 2) + 1) ≤ 2 ^ (2 * (Lq q / 2) - 2) :=
      Nat.le_of_mul_le_mul_right h8 (by norm_num)
    have h3 : 2 ^ (2 * (Lq q / 2) - 2) ≤ 2 ^ (Lq q - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : rowBr cr q ≤ 2 * (Lq q / 2) + 1 := by omega
    have hkey : 2 ^ (Lq q / 2 + 1) * rowBr cr q ≤ q :=
      (Nat.mul_le_mul_left _ h1).trans (h2.trans (h3.trans hq1))
    have hdiv : 2 ^ (Lq q / 2 + 1) ≤ q / rowBr cr q := (Nat.le_div_iff_mul_le (by omega)).2 hkey
    have hlog : Lq q / 2 + 1 ≤ Nat.log 2 (q / rowBr cr q + 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    unfold starWidth
    calc Lq q ≤ 2 * (Lq q / 2 + 1) := by omega
      _ ≤ rowBr cr q * Nat.log 2 (q / rowBr cr q + 1) := Nat.mul_le_mul hr2 hlog
  · calc starWidth (rowBr cr q) q ≤ rowBr cr q * Lq q := starWidth_le _ q
      _ ≤ Lq q * Lq q := Nat.mul_le_mul_right _ (by omega)
      _ = Lq q ^ 2 := by ring
      _ ≤ Lq q ^ kDeg := Nat.pow_le_pow_right (by have := Lq_pos q; omega) hk

end Star

section Cap
open NearCubicWires.WireExponent3_5.Shared (StarParams)

theorem hcap_of (C : CapParams) (m : Mode) (P : StarParams) (s W q : ℕ) (hq : 1 ≤ q) (hn : P.n = q)
    (hβ : 1 ≤ C.betaInv) (β : ℝ) (hβle : 1 / (C.betaInv : ℝ) ≤ β) (hW : (W : ℝ) ≤ wireCap C m q) :
    P.popRate * ((s : ℝ) * W + C.Cpar * (q : ℝ) ^ 2) ≤ β * (rowBCap C m P.r s q : ℝ) := by
  have hcomp := rowBCap_complete C m P.r s q hq hβ
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq'
  have hrate : P.popRate = 4 * Real.sqrt 2 * ((P.r : ℝ) * Real.sqrt P.r) / ((q : ℝ) * Real.sqrt q) := by
    unfold StarParams.popRate; rw [hn]
  have hb : (0 : ℝ) < C.betaInv := by exact_mod_cast hβ
  have hcap0 : (0 : ℝ) ≤ rowBCap C m P.r s q := Nat.cast_nonneg _
  calc P.popRate * ((s : ℝ) * W + C.Cpar * (q : ℝ) ^ 2)
      ≤ P.popRate * ((s : ℝ) * wireCap C m q + C.Cpar * (q : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Stars.popRate_nonneg P)
        have := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
        linarith
    _ = 4 * Real.sqrt 2 * ((P.r : ℝ) * Real.sqrt P.r) * ((s : ℝ) * wireCap C m q + C.Cpar * (q : ℝ) ^ 2) /
          ((q : ℝ) * Real.sqrt q) := by rw [hrate]; ring
    _ ≤ (rowBCap C m P.r s q : ℝ) / C.betaInv := hcomp
    _ = (1 / (C.betaInv : ℝ)) * (rowBCap C m P.r s q : ℝ) := by ring
    _ ≤ β * (rowBCap C m P.r s q : ℝ) := mul_le_mul_of_nonneg_right hβle hcap0

end Cap

end NearCubicWires.WireExponent3_5.Transfer

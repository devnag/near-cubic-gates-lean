import Proof.Wire_3_5.RecoveryLedgerAt
import Proof.Wire_3_5.RecoveryCaseOne
import Proof.Foundations.PolynomialSchedule

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open Filter

/-! ## One more XOR copy -/

theorem xorEpsilon_succ_lt (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 2) (t : ℕ) (ht : 1 ≤ t) :
    xorEpsilon δ (t + 1) < xorEpsilon δ t := by
  unfold xorEpsilon
  have e : t + 1 - 1 = (t - 1) + 1 := by omega
  rw [e, pow_succ]
  have ha : 0 < (1 - δ) ^ (t - 1) := pow_pos (by linarith) _
  have hb : 0 < 1 / 2 - δ := by linarith
  have hp := mul_pos (mul_pos ha h0) hb
  have e2 : (1 - δ) ^ (t - 1) * (1 - δ) * (1 / 2 - δ) =
      (1 - δ) ^ (t - 1) * (1 / 2 - δ) - (1 - δ) ^ (t - 1) * δ * (1 / 2 - δ) := by ring
  rw [e2]; linarith

/-! ## The per-atom caps -/

theorem wireCap_nonneg (C : CapParams) (m : Mode) (q : ℕ) : 0 ≤ wireCap C m q := by
  unfold wireCap; positivity

/-- `q ≤ w_i(q)` eventually (the exponent `K_i ≤ 6` and `L⁶ ≤ q`). -/
theorem eventually_wireCap_ge (C : CapParams) (m : Mode) (hc : 1 ≤ C.coef m) :
    ∀ᶠ q : ℕ in atTop, (q : ℝ) ≤ wireCap C m q := by
  filter_upwards [eventually_mul_Lq_pow_le 1 6, eventually_ge_atTop 1] with q hL hq1
  unfold wireCap
  have hL1 : (1 : ℝ) ≤ (Lq q : ℝ) := by exact_mod_cast Lq_pos q
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have he : ((capExp32 m : ℝ) / 32) ≤ 6 := by cases m <;> norm_num [capExp32]
  have hLe : (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) ≤ (Lq q : ℝ) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 he
  have hL6 : (Lq q : ℝ) ^ (6 : ℝ) ≤ q := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h6 : Lq q ^ 6 ≤ q := by simpa using hL
    exact_mod_cast h6
  have hpos : 0 < (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) := Real.rpow_pos_of_pos (by linarith) _
  rw [le_div_iff₀ hpos]
  have hsq : 1 ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hq0
    rwa [Real.sqrt_one] at h
  have hc' : (1 : ℝ) ≤ (C.coef m : ℝ) := by exact_mod_cast hc
  have hqq : (q : ℝ) * q ≤ (q : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hq0 (mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q) : (0 : ℝ) ≤ q * q)
    nlinarith [h]
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  calc (q : ℝ) * (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) ≤ (q : ℝ) * q :=
        mul_le_mul_of_nonneg_left (hLe.trans hL6) (Nat.cast_nonneg q)
    _ ≤ (q : ℝ) ^ 3 := hqq
    _ = 1 * (q : ℝ) ^ 3 * 1 := by ring
    _ ≤ (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q := by gcongr

/-- `w_i(q) ≤ q⁴` eventually (`a_i ≤ √q`). -/
theorem eventually_wireCap_le (C : CapParams) (m : Mode) :
    ∀ᶠ q : ℕ in atTop, wireCap C m q ≤ (q : ℝ) ^ 4 := by
  filter_upwards [eventually_ge_atTop (C.coef m ^ 2)] with q hq
  unfold wireCap
  have hL1 : (1 : ℝ) ≤ (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32) :=
    Real.one_le_rpow (by exact_mod_cast Lq_pos q) (by positivity)
  have hnum0 : 0 ≤ (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q := by positivity
  have hc : (C.coef m : ℝ) ≤ Real.sqrt q := by
    have h1 : ((C.coef m : ℝ)) ^ 2 ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by positivity)
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  calc (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q / (Lq q : ℝ) ^ ((capExp32 m : ℝ) / 32)
      ≤ (C.coef m : ℝ) * (q : ℝ) ^ 3 * Real.sqrt q := div_le_self hnum0 hL1
    _ = (q : ℝ) ^ 3 * ((C.coef m : ℝ) * Real.sqrt q) := by ring
    _ ≤ (q : ℝ) ^ 3 * (Real.sqrt q * Real.sqrt q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) hq3
    _ = (q : ℝ) ^ 4 := by rw [hs]; ring

/-- The integer cap `⌊w_i(q)⌋` from the two real bounds. -/
theorem floorCap_facts (C : CapParams) (m : Mode) (q : ℕ) (hge : (q : ℝ) ≤ wireCap C m q)
    (hle : wireCap C m q ≤ (q : ℝ) ^ 4) :
    q ≤ ⌊wireCap C m q⌋₊ ∧ ⌊wireCap C m q⌋₊ + 1 ≤ 2 * (q + 1) ^ 4 := by
  refine ⟨Nat.le_floor hge, ?_⟩
  have h1 : ⌊wireCap C m q⌋₊ ≤ q ^ 4 := Nat.floor_le_of_le (by push_cast; exact hle)
  have h2 : q ^ 4 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h3 : 1 ≤ (q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ## The grid and the clause width -/

/-- `s(q) ≤ q` eventually (`s⁸ ≤ C_sp L³`). -/
theorem eventually_sp_le (P : RowBParams) : ∀ᶠ q : ℕ in atTop, P.sp q ≤ q := by
  filter_upwards [eventually_mul_Lq_pow_le P.Csp 3] with q hq
  have h := (P.sp_le q).trans hq
  rcases Nat.eq_zero_or_pos (P.sp q) with h0 | h0
  · omega
  · exact (Nat.le_self_pow (by norm_num) _).trans h

/-- `⌈d_G log₂(q+2)⌉ ≤ q` eventually. -/
theorem eventually_clauseWidth_le (dG : ℕ) : ∀ᶠ q : ℕ in atTop, clauseWidth dG q ≤ q := by
  filter_upwards [eventually_mul_Lq_pow_le dG 1] with q hq
  unfold clauseWidth
  have h := clog_pow_le (q + 2) dG
  simp only [pow_one] at hq
  unfold Lq at hq
  omega

/-- A clause count `2^b ≤ X` has `b ≤ ⌈log₂ X⌉`. -/
theorem clauseBits_le (cb X : ℕ) (h : 2 ^ cb ≤ X) : cb ≤ Nat.clog 2 X :=
  (Nat.le_log_of_pow_le (by norm_num) h).trans (Nat.log_le_clog 2 X)

/-! ## The guess budget as a fixed polynomial of `q` -/

section BudgetPoly
variable (l : Literals)

/-- The oracle size exponent `2^{oracleDepth G}` (`q^G ≤ (q+1)^{2^{oracleDepth G}}`). -/
noncomputable def recOracleExp : ℕ := 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l)

/-- The size coefficient of the substituted request (`requestSize_le`). -/
noncomputable def recKs (kclk : ℕ) : ℕ :=
  3 * (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.coefficient +
    24 * (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.coefficient ^ 3 +
      (gatePCPP l).minimumArity + 3

/-- The oracle code bound `K_O(q)`. -/
noncomputable def recKo (q : ℕ) : ℕ :=
  2 * canonicalBooleanCircuitCodeBitBound ((q + 1) ^ recOracleExp l + 4) + 1

/-- The atom code bound `K_c(q)` at the description envelope `(q+1)^{26}`. -/
def recKc (q : ℕ) : ℕ :=
  2 * (canonicalSymmetricCircuitCodeBitBound ((q + 1) ^ 26 + 4) +
    canonicalThresholdCircuitCodeBitBound ((q + 1) ^ 26 + 4)) + 1

/-- The PCPP variable count bound `n_v(q)`. -/
noncomputable def recNv (kclk q : ℕ) : ℕ :=
  (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree +
    (gatePCPP l).coefficient * (recKs l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree

/-- **The guess-length envelope** `1 + K_O + n_v·q·(4 + K_c)`. -/
noncomputable def recBudget (kclk q : ℕ) : ℕ := 1 + recKo l q + recNv l kclk q * (q * (4 + recKc q))

theorem pb_succ_pow (e k : ℕ) : PolynomiallyBounded (fun q => (q + 1) ^ e + k) :=
  ⟨k + 1, e, by omega, fun n => by
    show (n + 1) ^ e + k ≤ (k + 1) * (n + 1) ^ e
    have h1 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    have h2 : k * 1 ≤ k * (n + 1) ^ e := Nat.mul_le_mul_left k h1
    have e2 : (k + 1) * (n + 1) ^ e = k * (n + 1) ^ e + (n + 1) ^ e := by ring
    omega⟩

theorem pb_succ_pow' (e : ℕ) : PolynomiallyBounded (fun q => (q + 1) ^ e) :=
  polynomiallyBounded_mono (fun _ => Nat.le_add_right _ 0) (pb_succ_pow e 0)

/-- **The guess-length envelope is a fixed polynomial of `q`.** -/
theorem recBudget_poly (kclk : ℕ) : PolynomiallyBounded (recBudget l kclk) := by
  have hO : PolynomiallyBounded (recKo l) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_comp PCPPQueryBounds.circuit_polynomial (pb_succ_pow (recOracleExp l) 4)))
      (polynomiallyBounded_constant 1)
  have hS : PolynomiallyBounded (fun q => canonicalSymmetricCircuitCodeBitBound ((q + 1) ^ 26 + 4)) :=
    polynomiallyBounded_comp SourceBudget.symWidth_poly (pb_succ_pow 26 4)
  have hT : PolynomiallyBounded (fun q => canonicalThresholdCircuitCodeBitBound ((q + 1) ^ 26 + 4)) :=
    polynomiallyBounded_comp SourceBudget.thrWidth_poly (pb_succ_pow 26 4)
  have hKc : PolynomiallyBounded recKc :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_add hS hT)) (polynomiallyBounded_constant 1)
  have hA : PolynomiallyBounded (fun q => (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant _) (pb_succ_pow' _)
  have hB : PolynomiallyBounded
      (fun q => (gatePCPP l).coefficient * (recKs l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant _)
      (polynomiallyBounded_pow (polynomiallyBounded_mul (polynomiallyBounded_constant _) (pb_succ_pow' _)) _)
  have hNv : PolynomiallyBounded (recNv l kclk) := polynomiallyBounded_add hA hB
  have hQ : PolynomiallyBounded (fun q => q * (4 + recKc q)) :=
    polynomiallyBounded_mul polynomiallyBounded_id (polynomiallyBounded_add (polynomiallyBounded_constant 4) hKc)
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_constant 1) hO)
    (polynomiallyBounded_mul hNv hQ)

end BudgetPoly

/-! ## The per-width facts -/

/-- **The recovery's per-width facts** at the width `q`. -/
structure RecQ (l : Literals) (G : Split.Gate) (q : ℕ) : Prop where
  two : 2 ≤ q
  big : 75894 ≤ q + 1
  star : Even (rowBr G.row.cr q) ∧ 2 ≤ rowBr G.row.cr q ∧ 4 * rowBr G.row.cr q ≤ q ∧
    Lq q ≤ starWidth (rowBr G.row.cr q) q ∧ starWidth (rowBr G.row.cr q) q ≤ Lq q ^ G.kDeg
  capS : q ≤ ⌊wireCap G.row.cap .sym q⌋₊ ∧ ⌊wireCap G.row.cap .sym q⌋₊ + 1 ≤ 2 * (q + 1) ^ 4
  capT : q ≤ ⌊wireCap G.row.cap .thr q⌋₊ ∧ ⌊wireCap G.row.cap .thr q⌋₊ + 1 ≤ 2 * (q + 1) ^ 4
  sp : G.row.sp q ≤ q
  cw : clauseWidth (recDG l) q ≤ q
  xi : 1 / (2 : ℝ) ^ (G.filterErrDeg * Nat.clog 2 (q + 2)) ≤ ((gateCParams1 l).ξ : ℝ)
  hD : (1 + (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ)) ^ 4 * (q : ℝ) ^ (-(G.D : ℝ)) ≤
    ((gateParams1 l).eps0 : ℝ)
  pow17 : 12800 * (q + 1) ^ 16 ≤ q ^ 17
  adv1 : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * l.eightSources.amplification.stvExponent) q : ℝ)
      (-(1 : ℝ) / l.eightSources.amplification.stvExponent) <
    xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)
  copies : (selectedAmplifier l.eightSources.amplification (recOracleDeg l)).arityCoefficient ≤
    recCopies (gateZeta_pos l) (gateZeta_lt l) q

/-- **The per-width facts hold eventually** at the gate constants. -/
theorem eventually_recQ (l : Literals) (G : Split.Gate) (hG : GateRel l G) : ∀ᶠ q : ℕ in atTop, RecQ l G q := by
  have hξ : (0 : ℝ) < ((gateCParams1 l).ξ : ℝ) := by
    have e : (gateCParams1 l).ξ = gateEps l / 100 := rfl
    have := gateEps_pos l
    rw [e]; push_cast; positivity
  have he0 : (0 : ℝ) < ((gateParams1 l).eps0 : ℝ) := by
    have e : (gateParams1 l).eps0 = gateEps l ^ 2 / 20000 := rfl
    have := gateEps_pos l
    rw [e]; push_cast; positivity
  have hf : 1 ≤ G.filterErrDeg := by have := G.hG7; omega
  have hcop : ∀ᶠ q : ℕ in atTop,
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)).arityCoefficient ≤
        recCopies (gateZeta_pos l) (gateZeta_lt l) q :=
    (recSchedule (gateZeta_pos l) (gateZeta_lt l) 0 0 0).t_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 75894, eventually_star G.row.cr G.row.cr_pos G.kDeg hG.kdeg,
    eventually_wireCap_ge G.row.cap .sym hG.aS, eventually_wireCap_le G.row.cap .sym,
    eventually_wireCap_ge G.row.cap .thr hG.aT, eventually_wireCap_le G.row.cap .thr,
    eventually_sp_le G.row, eventually_clauseWidth_le (recDG l),
    eventually_hξ G.filterErrDeg hf _ hξ, eventually_hD (gateZeta_pos l) (gateZeta_lt l) G.D G.D_pos _ he0,
    eventually_12800,
    eventually_caseOne_adv (gateZeta_pos l) (gateZeta_lt l) _ l.eightSources.amplification.stvExponentPositive,
    hcop] with q hq hstar hS1 hS2 hT1 hT2 hsp hcw hxi hD h17 hadv hc
  exact ⟨by omega, by omega, hstar, floorCap_facts _ _ q hS1 hS2, floorCap_facts _ _ q hT1 hT2, hsp, hcw, hxi, hD,
    h17, hadv, hc⟩

end NearCubicWires.WireExponent3_5.Transfer

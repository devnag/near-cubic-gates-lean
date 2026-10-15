import Proof.CaseAnalysis.RawRowsPaperShape

/-! The paper's coefficient is chosen after fixed resource constants. One
subsequent arity onset absorbs the lower logarithmic term. No clock-dependent
preprocessing exponent or extra imported resource premise is introduced. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierCapacity
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def capDenominator (A kappa : ℕ) := (1600*(A+1))^2*(4*kappa+1)+1
noncomputable def paperCap (A kappa : ℕ) : ℝ := 1/(capDenominator A kappa : ℝ)

theorem paperCap_positive (A kappa : ℕ) : 0 < paperCap A kappa := by
  unfold paperCap capDenominator
  positivity

theorem paperCap_le_one (A kappa : ℕ) : paperCap A kappa ≤ 1 := by
  have hD : (1 : ℝ) ≤ capDenominator A kappa := by
    unfold capDenominator
    exact_mod_cast (by omega : 1 ≤ (1600*(A+1))^2*(4*kappa+1)+1)
  unfold paperCap
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < capDenominator A kappa)).2
  linarith

theorem cap_scaled (A kappa : ℕ) :
    4*(kappa : ℝ)*paperCap A kappa*(1600*((A : ℝ)+1))^2 ≤ 1 := by
  have hD : (0 : ℝ) < capDenominator A kappa := by unfold capDenominator; positivity
  unfold paperCap
  rw [show 4*(kappa : ℝ)*(1/(capDenominator A kappa : ℝ))*(1600*((A : ℝ)+1))^2=
    (4*kappa*(1600*((A : ℝ)+1))^2)/(capDenominator A kappa : ℝ) by ring]
  apply (div_le_iff₀ hD).2
  unfold capDenominator
  push_cast
  nlinarith [sq_nonneg (1600*((A : ℝ)+1))]

theorem cap_root_bound (A kappa r q active : ℕ) (logarithm : ℝ)
    (hlog : 0 ≤ logarithm)
    (hcap : (active : ℝ)*logarithm^(2*r+4) ≤ 4*kappa*paperCap A kappa*(q : ℝ)^2) :
    1600*(A : ℝ)*Real.sqrt active*logarithm^(r+2) ≤ q := by
  have hs := mul_le_mul_of_nonneg_left hcap (sq_nonneg (1600*((A : ℝ)+1)))
  have hc := mul_le_mul_of_nonneg_right (cap_scaled A kappa) (sq_nonneg (q : ℝ))
  have hweighted : (1600*((A : ℝ)+1))^2*active*logarithm^(2*r+4) ≤ (q : ℝ)^2 := by
    nlinarith only [hs,hc]
  have he : (logarithm^(r+2))^2=logarithm^(2*r+4) := by rw [←pow_mul]; congr 1; omega
  have hsq : (1600*((A : ℝ)+1)*Real.sqrt active*logarithm^(r+2))^2 ≤ (q : ℝ)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),he]
    exact hweighted
  have hlarge : 1600*((A : ℝ)+1)*Real.sqrt active*logarithm^(r+2) ≤ q := by
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hmono : 1600*(A : ℝ)*Real.sqrt active*logarithm^(r+2) ≤
      1600*((A : ℝ)+1)*Real.sqrt active*logarithm^(r+2) := by gcongr; linarith
  exact hmono.trans hlarge

theorem paper_margin_eventual (A kappa r : ℕ) :
    ∃ onset, ∀ q, onset ≤ q → ∀ active K cost : ℕ,
      K ≤ kappa*logScale q →
      (active : ℝ)*(logScale q : ℝ)^(2*r+4) ≤
        4*kappa*paperCap A kappa*(q : ℝ)^2 →
      (cost : ℝ) ≤ A*(Real.sqrt active+(logScale q : ℝ))*(logScale q : ℝ)^(r+2) →
      200*cost ≤ q-K ∧ 67 ≤ q-K := by
  obtain ⟨n₁,hn₁⟩ := coefficient_mul_logScale_pow_eventually_le (1600*A) (r+3)
  obtain ⟨n₂,hn₂⟩ := coefficient_mul_logScale_pow_eventually_le (2*kappa) 1
  refine ⟨max 134 (max n₁ n₂),?_⟩
  intro q hq active K cost hK hcap hcost
  have hn1 : n₁ ≤ q := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hq)
  have hn2 : n₂ ≤ q := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hq)
  have hq134 : 134 ≤ q := (Nat.le_max_left _ _).trans hq
  have hlower : 1600*(A : ℝ)*(logScale q : ℝ)^(r+3) ≤ q := by exact_mod_cast hn₁ q hn1
  have hlive : 2*K ≤ q := by
    have h := hn₂ q hn2
    simp only [pow_one] at h
    nlinarith
  have hroot := cap_root_bound A kappa r q active (logScale q) (by positivity) hcap
  have he : (logScale q : ℝ)^(r+3)=(logScale q : ℝ)*(logScale q : ℝ)^(r+2) := by
    rw [show r+3=(r+2)+1 by omega,pow_succ']
  rw [he] at hlower
  have hcost' : 800*(cost : ℝ) ≤ q := by nlinarith only [hroot,hlower,hcost]
  have hnat : 800*cost ≤ q := by exact_mod_cast hcost'
  constructor <;> omega

end
end NearCubicWires.RepairSource.CloseoutRawRows

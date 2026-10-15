import Proof.CaseAnalysis.RowsEstimatorDriverRun

/-! Producing and later cleaning the driver retains a single table factor.
Every arithmetic cost is linear in its actual unary result. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_linear (a : WilliamsAlgorithm) (d p G C : ℕ) :
    budget a d p G C ≤ (10*e a+1000)*(Driver.value a d p G C+1) := by
  let S := d+p
  let M := S+G
  let Ct := 64*(C+1)
  let Mt := 2000000*(M+1)^3
  let Tp := Driver.tableCoefficient a*(S+1)^(e a)
  let U := 2^d
  let T := U^2*Tp
  let V := Ct+Mt+T
  have hv : Driver.value a d p G C=V := by
    dsimp [Driver.value,Driver.tableValue,V,Ct,Mt,T,U,Tp,M,S]
    ring
  have he : 1 ≤ e a := by unfold e CompetitorCrossScheduler.exponent;omega
  have hcoef : 1 ≤ Driver.tableCoefficient a := by
    have hp : 1 ≤ 2^(e a) := Nat.one_le_pow _ _ (by decide)
    have hc : 1 ≤ CompetitorCountTableRecord.coefficient a+1 := by omega
    change 1 ≤ 4*2^(e a)*(CompetitorCountTableRecord.coefficient a+1)
    nlinarith only [hp,hc]
  have hu : 1 ≤ U := Nat.one_le_pow _ _ (by decide)
  have hu2 : 1 ≤ U^2 := Nat.one_le_pow _ _ hu
  have hsp : S+1 ≤ (S+1)^(e a) := Nat.le_self_pow (by omega) _
  have htp : S+1 ≤ Tp := hsp.trans (by dsimp [Tp];simpa only [one_mul] using Nat.mul_le_mul_right ((S+1)^(e a)) hcoef)
  have htp1 : 1 ≤ Tp := by omega
  have hTpT : Tp ≤ T := by dsimp [T];simpa only [one_mul] using Nat.mul_le_mul_right Tp hu2
  have hU2T : U^2 ≤ T := by dsimp [T];simpa only [mul_one] using Nat.mul_le_mul_left (U^2) htp1
  have hU2 : U ≤ U^2 := by simpa only [pow_two] using Nat.le_mul_self U
  have hdTp : d ≤ Tp := by dsimp [S] at htp;omega
  have hdU : d*U ≤ T := by
    calc
      d*U ≤ Tp*(U^2) := Nat.mul_le_mul hdTp hU2
      _ = T := by dsimp [T];ring
  have hm : M+1 ≤ (M+1)^3 := Nat.le_self_pow (by decide) _
  have hM : M ≤ Mt := by dsimp [Mt];omega
  have hCtV : Ct ≤ V := by dsimp [V];omega
  have hMtV : Mt ≤ V := by dsimp [V];omega
  have hTV : T ≤ V := by dsimp [V];omega
  have hTpV : Tp ≤ V := hTpT.trans hTV
  have hU2V : U^2 ≤ V := hU2T.trans hTV
  have hUV : U ≤ V := hU2.trans hU2V
  have hdUV : d*U ≤ V := hdU.trans hTV
  have hMV : M ≤ V := hM.trans hMtV
  have hSV : S ≤ V := by dsimp [M] at hMV;omega
  have hdV : d ≤ V := by dsimp [S] at hSV;omega
  have h0 : 2*S+6 ≤ 8*(V+1) := by omega
  have h1 : 2*M+6 ≤ 8*(V+1) := by omega
  have h2 : DriverPower.budget 1 64 C ≤ 30*(V+1) := by
    have h := DriverPower.budget_linear 1 64 C (by decide) (by decide)
    dsimp [Ct] at hCtV
    simpa only [pow_one] using h.trans (by nlinarith only [hCtV])
  have h3 : DriverPower.budget 3 2000000 M ≤ 50*(V+1) := by
    have h := DriverPower.budget_linear 3 2000000 M (by decide) (by decide)
    exact h.trans (by dsimp [Mt] at hMtV;nlinarith only [hMtV])
  have h4 : DriverPower.budget (e a) (Driver.tableCoefficient a) S ≤ (10*e a+20)*(V+1) := by
    have h := DriverPower.budget_linear (e a) (Driver.tableCoefficient a) S he hcoef
    exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hTpV 1))
  have h5 : CompetitorCrossRequestHeaders.powerBudget d ≤ 500*(V+1) := by
    unfold CompetitorCrossRequestHeaders.powerBudget MatrixScorePower.budget MatrixUnaryTemplate.budget
    change 2*(8*d+40+(U*(8*(d+3)+10)+8*(d+3)+U+17))+2 ≤ _
    nlinarith only [hUV,hdUV,hdV]
  have h6 : DimensionPower.cost 1 U 2 ≤ 38*(V+1) := by
    have h := DriverPower.cost_linear 2 1 U 2 le_rfl hu
    norm_num at h
    nlinarith only [h,hU2V]
  have h7 : 2*Tp+8 ≤ 10*(V+1) := by omega
  have h8 : WilliamsUnaryProduct.budget (U^2) Tp ≤ 16*(V+1) := by
    unfold WilliamsUnaryProduct.budget
    dsimp [T] at hTV
    nlinarith only [hTV,hU2V]
  have h9 : 2*(Ct+Mt)+6 ≤ 8*(V+1) := by dsimp [V];omega
  have h10 : 2*(Ct+Mt+T)+6 ≤ 8*(V+1) := by dsimp [V];omega
  rw [hv]
  change ((((((((((2*S+6)+1+(2*M+6))+1+DriverPower.budget 1 64 C)+1+
    DriverPower.budget 3 2000000 M)+1+DriverPower.budget (e a) (Driver.tableCoefficient a) S)+1+
    CompetitorCrossRequestHeaders.powerBudget d)+1+DimensionPower.cost 1 U 2)+1+
    (2*Tp+8))+1+WilliamsUnaryProduct.budget (U^2) Tp)+1+(2*(Ct+Mt)+6))+1+
    (2*(Ct+Mt+T)+6) ≤ _
  nlinarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout

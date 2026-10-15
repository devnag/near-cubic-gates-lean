import Proof.CaseAnalysis.RowsCapacityDriver
import Proof.CaseAnalysis.RowsPreparedPolynomial

/-! Paid preparation is linear in the one digit exponential. The actual
native widths remain in a fixed polynomial factor outside that exponential. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCapacityBudget
open RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem driver_bound (S R : ℕ) :
    CloseoutRowsCapacityDriver.budget S R ≤ 1000000*2^R*(S+1)^5*(R+1) := by
  have ht : 1 ≤ (S+1)^5 := Nat.one_le_pow 5 (S+1) (by omega)
  have he : 1 ≤ 2^R := Nat.one_le_two_pow
  have hs4 : S^4 ≤ (S+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hd := DimensionPower.cost_bound 4 4096 S 4 (by decide)
  have hd' : DimensionPower.cost 4096 S 4 ≤ 110000*(S+1)^5 := by norm_num at hd; omega
  have hc : RecoveryPCPFormulaResumeCountCold.budget R ≤ 100*2^R*(R+1) := by
    have hr : R+1 ≤ 2^R*(R+1) := by nlinarith [Nat.mul_le_mul_right (R+1) he]
    unfold RecoveryPCPFormulaResumeCountCold.budget RecoveryPCPFormulaResumeCount.budget
    nlinarith
  have hsucc : 2*(2^R-1)+6 ≤ 8*2^R := by omega
  have hp : WilliamsUnaryProduct.budget (4096*S^4) (2^R) ≤ 41000*2^R*(S+1)^5 := by
    have hs4e : S^4 ≤ 2^R*(S+1)^5 :=
      hs4.trans (by nlinarith [Nat.mul_le_mul_right ((S+1)^5) he])
    have hs4e' : S^4*2^R ≤ 2^R*(S+1)^5 := by nlinarith [Nat.mul_le_mul_right (2^R) hs4]
    have hte : 1 ≤ 2^R*(S+1)^5 := by nlinarith
    unfold WilliamsUnaryProduct.budget
    nlinarith
  have hE : 2^R ≤ 2^R*(S+1)^5*(R+1) := by nlinarith [Nat.mul_le_mul_left (2^R) ht]
  have hT : (S+1)^5 ≤ 2^R*(S+1)^5*(R+1) := by nlinarith [Nat.mul_le_mul_right ((S+1)^5) he]
  have hER : 2^R*(R+1) ≤ 2^R*(S+1)^5*(R+1) := by
    nlinarith [Nat.mul_le_mul_left (2^R*(R+1)) ht]
  have hET : 2^R*(S+1)^5 ≤ 2^R*(S+1)^5*(R+1) := by nlinarith
  unfold CloseoutRowsCapacityDriver.budget
  nlinarith

theorem loop_bound (S R Q : ℕ) (hQ : Q ≤ S) :
    CloseoutRowsDegreeLoop.budget Q (4096*S^4*2^R) ≤ 200000*2^R*(S+1)^5 := by
  have he : 1 ≤ 2^R := Nat.one_le_two_pow
  have ht : 1 ≤ (S+1)^5 := Nat.one_le_pow 5 (S+1) (by omega)
  have hs5 : S^5 ≤ (S+1)^5 := Nat.pow_le_pow_left (Nat.le_succ S) 5
  have hs : S ≤ (S+1)^5 := (Nat.le_succ S).trans (Nat.le_self_pow (by decide) (S+1))
  have hse : S ≤ 2^R*(S+1)^5 := hs.trans (by nlinarith [Nat.mul_le_mul_right ((S+1)^5) he])
  have hte : 1 ≤ 2^R*(S+1)^5 := by nlinarith
  unfold CloseoutRowsDegreeLoop.budget
  calc
    _ ≤ S*(40*(4096*S^4*2^R)+103)+3 := by gcongr
    _ ≤ 200000*2^R*(S+1)^5 := by
      nlinarith [Nat.mul_le_mul_left (2^R) hs5]

theorem preparation_bound (n p F w N Q : ℕ) :
    CloseoutRowsCapacityDriver.budget (CloseoutRowsPreparationBounds.scale n p F w N Q) (w*(Q+1)) +
      CloseoutRowsDegreeLoop.budget Q (CloseoutRowsPreparationBounds.capacity n p F w N Q) ≤
      1200000*2^(w*(Q+1))*(CloseoutRowsPreparationBounds.scale n p F w N Q+1)^5*(w*(Q+1)+1) := by
  have hd := driver_bound (CloseoutRowsPreparationBounds.scale n p F w N Q) (w*(Q+1))
  have hl := loop_bound (CloseoutRowsPreparationBounds.scale n p F w N Q) (w*(Q+1)) Q
    (by unfold CloseoutRowsPreparationBounds.scale; omega)
  change CloseoutRowsCapacityDriver.budget _ _+CloseoutRowsDegreeLoop.budget Q (4096*_ ^4*2^_) ≤ _
  have hmul := Nat.mul_le_mul_left
    (200000*2^(w*(Q+1))*(CloseoutRowsPreparationBounds.scale n p F w N Q+1)^5)
    (show 1 ≤ w*(Q+1)+1 by omega)
  simp only [Nat.mul_one] at hmul
  calc
    _ ≤ 1000000*2^(w*(Q+1))*(CloseoutRowsPreparationBounds.scale n p F w N Q+1)^5*(w*(Q+1)+1) +
        200000*2^(w*(Q+1))*(CloseoutRowsPreparationBounds.scale n p F w N Q+1)^5*(w*(Q+1)+1) :=
      Nat.add_le_add hd (hl.trans hmul)
    _ = _ := by ring

end NearCubicWires.RepairOrdinary.CloseoutRowsCapacityBudget

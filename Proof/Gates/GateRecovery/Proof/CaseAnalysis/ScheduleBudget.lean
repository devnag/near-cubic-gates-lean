import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleLoop
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleNativeBudget
import Proof.CaseAnalysis.CapacityBudget
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.NativeWidthPolynomial

namespace GR

/-! One all-index resource bound for the actual schedule test. Constants
may depend on the fixed recovery clock; this is solely a paper C.12 charge. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem test_budget_uniform (sources : GateEightSources) (k D copies ext : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) :
    ∃ coefficient degree : Nat, ∀ n s, s ≤ n →
      Test.budget sources k D copies ext clock s n+1 ≤ coefficient*(2^n+1)^degree := by
  obtain ⟨a,d,hnative⟩ := native_budget sources k clock
  let Q := sources.width.width 0+sources.width.jump+3
  let b := DimensionPolynomial.coefficient D 1+(64*(2*copies)+256)*(ext+1)^2+4*ext+1000
  let R := copies*(D+ext+1)*Q
  refine ⟨a+b*Q^(2*D+2)+4*R+600,d+2*D+2,?_⟩
  intro n s hs
  let x : Nat := 2^n+1
  let P := x^(d+2*D+2)
  let q := sources.width.width s
  let m := CloseoutLanguage.widthAt sources k clock copies ext D s
  have hx : 1 ≤ x := Nat.succ_pos _
  have hn : n+1 ≤ x := by have := Nat.lt_two_pow_self (n := n); dsimp [x]; omega
  have hp : 2^s+1 ≤ x := Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hs) 1
  have hxP : x ≤ P := Nat.le_self_pow (by dsimp [P]; omega) _
  have hx2P : x^2 ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hdP : x^d ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have heP : x^(2*D+2) ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : q+3 ≤ Q*x := by
    have hb := CloseoutLanguage.native_dyadic_bound sources k clock s
    have h0 := Nat.mul_le_mul_left (sources.width.width 0) hx
    have hj := Nat.mul_le_mul_left (sources.width.jump) (show s ≤ x by omega)
    change q ≤ _ at hb
    dsimp only [Q]
    nlinarith
  have hm : m ≤ R*x := by
    have hc := CloseoutLanguage.clause_linear D q
    have hi : q+CloseoutLanguage.clauseWidth D q+(ext+1) ≤ (D+ext+1)*(q+1) := by nlinarith
    have hh := (Nat.mul_le_mul_left copies hi).trans
      (Nat.mul_le_mul_left copies (Nat.mul_le_mul_left (D+ext+1) (show q+1 ≤ Q*x by omega)))
    change copies*(q+CloseoutLanguage.clauseWidth D q+(ext+1)) ≤ _
    exact hh.trans_eq (by dsimp [R]; ring)
  have hpower : CloseoutCapacity.Power.budget s ≤ 384*P := by
    calc
      _ ≤ 128*(s+3)*(2^s+1) := CloseoutCapacity.power_budget s
      _ ≤ 128*(3*x)*x := Nat.mul_le_mul (Nat.mul_le_mul_left 128 (by omega)) hp
      _ = 384*x^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hx2P
  have hframe : 4*2^s+6 ≤ 10*P := by nlinarith
  have hnat : nativeBudget sources k clock s ≤ a*P := by
    have hb := hnative s
    exact hb.trans ((Nat.mul_le_mul_left a (Nat.pow_le_pow_left hp d)).trans
      (Nat.mul_le_mul_left a hdP))
  have hwidth : Width.budget D (2*copies) ext q ≤ b*Q^(2*D+2)*P := by
    calc
      _ ≤ b*(q+3)^(2*D+2) := Width.budget_bound D (2*copies) ext q hD
      _ ≤ b*(Q*x)^(2*D+2) := Nat.mul_le_mul_left b (Nat.pow_le_pow_left hq _)
      _ = b*Q^(2*D+2)*x^(2*D+2) := by rw [mul_pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ heP
  have hcompare : RawCompare.budget (2*m) n ≤ (4*R+17)*P := by
    have hmin := Nat.min_le_right (2*m) n
    have hb : RawCompare.budget (2*m) n ≤ (4*R+17)*x := by
      unfold RawCompare.budget
      nlinarith
    exact hb.trans (Nat.mul_le_mul_left _ hxP)
  change CloseoutCapacity.Power.budget s+1+(4*2^s+6)+1+
    nativeBudget sources k clock s+1+
    Width.budget D (2*copies) ext q+1+RawCompare.budget (2*m) n+1 ≤
      (a+b*Q^(2*D+2)+4*R+600)*P
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutSchedule

end GR

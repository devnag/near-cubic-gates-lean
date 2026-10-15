import Proof.CaseAnalysis.ScheduleLoop
import Proof.CaseAnalysis.ScheduleNativeBudget
import Proof.CaseAnalysis.CapacityBudget
import Proof.CaseAnalysis.NativeWidthPolynomial

/-! One all-index resource bound for the actual schedule test. Constants
may depend on the fixed recovery clock; this is solely a paper C.12 charge. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary ProjectionNormalization SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem test_budget_uniform (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) :
    ∃ coefficient degree : Nat, ∀ n s, s ≤ n →
      Test.budget sources k D copies clock s n+1 ≤ coefficient*(2^n+1)^degree := by
  obtain ⟨a,d,hnative⟩ := native_budget sources k clock
  let Q := (outer sources k clock).result.pcp.nativeWidth 1+
    CloseoutNativeWidth.nativeJump k (fixedProjection sources).degrees.proofLog+3
  let b := DimensionPolynomial.coefficient D 1+64*(2*copies)+900
  let R := copies*(D+1)*Q
  refine ⟨a+b*Q^(2*D+2)+4*R+600,d+2*D+2,?_⟩
  intro n s hs
  let x : Nat := 2^n+1
  let P := x^(d+2*D+2)
  let q := (outer sources k clock).result.pcp.nativeWidth (2^s)
  let m := CloseoutLanguage.widthAt sources k clock copies D s
  have hx : 1 ≤ x := Nat.succ_pos _
  have hn : n+1 ≤ x := by have := Nat.lt_two_pow_self (n := n); dsimp [x]; omega
  have hp : 2^s+1 ≤ x := Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hs) 1
  have hxP : x ≤ P := Nat.le_self_pow (by dsimp [P]; omega) _
  have hx2P : x^2 ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hdP : x^d ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have heP : x^(2*D+2) ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : q+3 ≤ Q*x := by
    have hb := CloseoutLanguage.native_dyadic_bound sources k clock s
    have h0 := Nat.mul_le_mul_left ((outer sources k clock).result.pcp.nativeWidth 1) hx
    have hj := Nat.mul_le_mul_left
      (CloseoutNativeWidth.nativeJump k (fixedProjection sources).degrees.proofLog)
      (show s ≤ x by omega)
    change q ≤ _ at hb
    dsimp only [Q]
    nlinarith
  have hm : m ≤ R*x := by
    have hc := CloseoutLanguage.clause_linear D q
    have hi : q+CloseoutLanguage.clauseWidth D q+1 ≤ (D+1)*(q+1) := by nlinarith
    have hh := (Nat.mul_le_mul_left copies hi).trans
      (Nat.mul_le_mul_left copies (Nat.mul_le_mul_left (D+1) (show q+1 ≤ Q*x by omega)))
    change copies*(q+CloseoutLanguage.clauseWidth D q+1) ≤ _
    exact hh.trans_eq (by dsimp [R]; ring)
  have hpower : CloseoutCapacity.Power.budget s ≤ 384*P := by
    calc
      _ ≤ 128*(s+3)*(2^s+1) := CloseoutCapacity.power_budget s
      _ ≤ 128*(3*x)*x := Nat.mul_le_mul (Nat.mul_le_mul_left 128 (by omega)) hp
      _ = 384*x^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hx2P
  have hframe : 4*2^s+6 ≤ 10*P := by nlinarith
  have hnat : nativeBudget sources k clock (List.replicate (2^s) true) ≤ a*P := by
    have hb := hnative (2^s) (fun _ => true)
    simp only [List.ofFn_const] at hb
    exact hb.trans ((Nat.mul_le_mul_left a (Nat.pow_le_pow_left hp d)).trans
      (Nat.mul_le_mul_left a hdP))
  have hwidth : Width.budget D (2*copies) q ≤ b*Q^(2*D+2)*P := by
    calc
      _ ≤ b*(q+3)^(2*D+2) := Width.budget_bound D (2*copies) q hD
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
    nativeBudget sources k clock (List.replicate (2^s) true)+1+
    Width.budget D (2*copies) q+1+RawCompare.budget (2*m) n+1 ≤
      (a+b*Q^(2*D+2)+4*R+600)*P
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutSchedule

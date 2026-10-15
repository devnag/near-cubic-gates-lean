import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleCoreWidth

namespace GR

namespace NearCubicWires.RepairSource.CloseoutSchedule.Width
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (D copies ext q : Nat) (hD : 1 ≤ D) :
    budget D copies ext q ≤
      (DimensionPolynomial.coefficient D 1+(64*copies+256)*(ext+1)^2+4*ext+1000)*(q+3)^(2*D+2) := by
  let A:=(q+2)^D
  let X:=(q+3)^(D+1)
  let P:=(q+3)^(2*D+2)
  let r:=CloseoutLanguage.clauseWidth D q
  let E:=(ext+1)^2
  have hAX : A ≤ X := (Nat.pow_le_pow_left (by omega : q+2 ≤ q+3) D).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hqX : q+3 ≤ X := Nat.le_self_pow (by omega) _
  have hXP : X^2=P := by dsimp [X,P];rw [←pow_mul];congr 1;ring
  have hqP : q+3 ≤ P := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ X := (show 1 ≤ q+3 by omega).trans hqX
  have hr : r ≤ A := Nat.clog_le_of_le_pow (RecoveryWitnessPolicy.self_le_two_pow A)
  have hA2 : (A+1)^2 ≤ 4*P := by
    have hs:=Nat.pow_le_pow_left (show A+1 ≤ 2*X by omega) 2
    rw [mul_pow,hXP] at hs
    exact hs
  have hr2 : (q+1+r+2)^2 ≤ 4*P := by
    have hs:=Nat.pow_le_pow_left (show q+1+r+2 ≤ 2*X by omega) 2
    rw [mul_pow,hXP] at hs
    exact hs
  have hlin : q+1+ext+r+2 ≤ (ext+1)*(q+1+r+2) := by nlinarith
  have hsq : (q+1+ext+r+2)^2 ≤ E*(4*P) := by
    have h:=Nat.pow_le_pow_left hlin 2
    rw [mul_pow] at h
    exact h.trans (Nat.mul_le_mul_left _ hr2)
  have hp:=DimensionPolynomial.budget_bound D 1 (q+1)
  have hc:=Clog.budget_bound A
  have hs:=Scale.budget_bound copies (q+1+ext) r
  have hcs:=Nat.mul_le_mul_left 128 hA2
  have hss:=Nat.mul_le_mul_left (16*copies+64) hsq
  have heP : ext ≤ ext*P := Nat.le_mul_of_pos_right _ (by omega)
  have he : q+1+2=q+3 := by omega
  rw [he] at hp
  change DimensionPolynomial.budget D 1 (q+1) ≤ DimensionPolynomial.coefficient D 1*P at hp
  change budget D copies ext q ≤ (DimensionPolynomial.coefficient D 1+(64*copies+256)*E+4*ext+1000)*P
  unfold budget Clause.budget
  change (2*q+4)+1+DimensionPolynomial.budget D 1 (q+1)+1+Clog.budget A+1+(2*ext+2)+1+(2*(q+1+ext)+6)+1+
    Scale.budget copies (q+1+ext) r ≤ _
  nlinarith

end NearCubicWires.RepairSource.CloseoutSchedule.Width

end GR

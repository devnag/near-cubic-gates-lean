import Proof.PCP.ProjectionDimensionPolynomial
import Proof.PCP.ProjectionDimensionPowerBounds

/-! The concrete polynomial evaluator has a fixed polynomial bound in its
short unary argument. All exponent dependence belongs to fixed log powers. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionPolynomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (D C : ℕ) := 16*C^2+74*C+6*D*C+7*D+44

theorem budget_bound (D C n : ℕ) :
    budget D C n ≤ coefficient D C*(n+2)^(2*D+2) := by
  let X := (n+2)^(2*D+2)
  have hx1 : 1 ≤ X := by dsimp [X]; exact Nat.one_le_pow _ _ (by omega)
  have hxn : n+2 ≤ X := by
    dsimp [X]
    exact Nat.le_self_pow (by omega) _
  have hpD : (n+2)^(D+1) ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
  have hpA : (n+1)^D ≤ (n+2)^D := Nat.pow_le_pow_left (by omega) D
  have hpAX : (n+2)^D ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
  have hval : value D C n ≤ C*X := Nat.mul_le_mul_left C (hpA.trans hpAX)
  have hp2 : ((n+1)^D)^2 ≤ X := by
    rw [←pow_mul]
    exact (Nat.pow_le_pow_left (by omega : n+1 ≤ n+2) (D*2)).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hval2 : (value D C n)^2 ≤ C^2*X := by
    rw [value,mul_pow]
    exact Nat.mul_le_mul_left _ hp2
  have hpow := DimensionPower.cost_bound D C (n+1) D le_rfl
  rw [show n+1+1=n+2 by omega] at hpow
  have hscaled := Nat.mul_le_mul_left (6*C) hpD
  have hpow' : DimensionPower.cost C (n+1) D ≤ (2*C+2+6*D*C+7*D)*X := by
    have hdc := Nat.mul_le_mul_left D hscaled
    have hconst := Nat.mul_le_mul_left (2*C+2+7*D) hx1
    nlinarith
  change budget D C n ≤ coefficient D C*X
  dsimp only [budget,coefficient]
  nlinarith

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionPolynomial

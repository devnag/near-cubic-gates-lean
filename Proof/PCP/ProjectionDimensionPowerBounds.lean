import Proof.PCP.ProjectionDimensionPower

/-! Uniform finite-degree bounds for the actual unary dimension evaluator. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionPower
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cost_bound (D C n j : ℕ) (hj : j ≤ D) :
    cost C n j ≤ 2*C+2+j*(6*C*(n+1)^(D+1)+7) := by
  induction j with
  | zero => simp [cost]
  | succ j ih =>
    have hprev := ih (by omega)
    have hp : n^j ≤ (n+1)^D :=
      (Nat.pow_le_pow_left (Nat.le_succ n) j).trans
        (Nat.pow_le_pow_right (by omega : 0<n+1) (by omega))
    have hmul := Nat.mul_le_mul hp (show 2*n+3 ≤ 3*(n+1) by omega)
    have he : (n+1)^D*(3*(n+1))=3*(n+1)^(D+1) := by rw [pow_succ]; ring
    rw [he] at hmul
    have hcm := Nat.mul_le_mul_left (2*C) hmul
    dsimp only [cost,RepairOrdinary.WilliamsUnaryProduct.budget]
    nlinarith

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionPower

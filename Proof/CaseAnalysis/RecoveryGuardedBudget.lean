import Proof.CaseAnalysis.RecoveryGuardedAppend

/-! A sufficient fixed cubic envelope for the actual guarded-selector head.
Paper C.12 only needs a fixed polynomial in the exponentially bounded graph
shape. This bound does not apply to the weak competitor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeGuarded
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (limit C : ℕ) : budget limit C ≤ 128*(limit+1)*(C+4) := by
  have small : RecoveryBoundedNativeUnaryPhase.trueBits.length ≤ 16 := by decide
  unfold budget RecoveryBoundedNativeUnaryJoin.budget
  nlinarith

theorem budget_cubic (limit W : ℕ) (hl : limit ≤ W) :
    budget limit (16384*(W+1)^2) ≤ 4194304*(W+1)^3 := by
  have one : 1 ≤ (W+1)^2 := by nlinarith
  calc
    budget limit (16384*(W+1)^2) ≤ 128*(limit+1)*(16384*(W+1)^2+4) :=
      budget_bound _ _
    _ ≤ 128*(W+1)*(16388*(W+1)^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 128 (by omega)) (by omega)
    _ = 2097664*(W+1)^3 := by ring
    _ ≤ 4194304*(W+1)^3 := Nat.mul_le_mul_right _ (by decide)

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeGuarded

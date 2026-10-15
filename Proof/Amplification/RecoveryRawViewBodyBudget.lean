import Proof.Amplification.RecoveryRawViewBodyMeaning

/-! Uniform cubic cost for the executed raw-view body. Literal counts are
bounded by the actual capped parser; all scratch sweeps and returns are paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (x : State) (hx : x.Valid) : budget x ≤ 33554432*(x.width+1)^3 := by
  have houter := RecoveryStoredListCell.time_bound x.outer.bits
  unfold RecoveryStoredListCell.budget at houter
  rw [hx.2.2.1] at houter
  have hclause := RecoveryRawClause.budget_bound x.width x.limit hx.2.2.2.2
  have hcap : x.capacity=8192*(x.width+1)^2 := rfl
  have hsq : (x.width+1)^2 ≤ (x.width+1)^3 := by
    calc
      _ ≤ (x.width+1)^2*(x.width+1) := by nlinarith [sq_nonneg (x.width : Nat)]
      _ = _ := by ring
  have hlinear : x.width+1 ≤ (x.width+1)^2 := by nlinarith [sq_nonneg (x.width : Nat)]
  have hlimit := hx.2.2.2.2
  unfold budget outerBudget clearBudget countBudget copyBudget clauseBudget clearCost
  rw [hcap]
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody

import Proof.CaseAnalysis.WitnessSupportCostRatio

/-! The factor-two comparison holds for the literal cold-family fuel,
including its original header, count loop and preparation overhead. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SupportCostRatio
open CloseoutRowsSupportStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_budget_le (S P H V before : ℕ) (bits : List Bool)
    (hp:FamilyResources.capacity S≤P) :
    before+FamilyCold.budget P H V (FamilyCosts.sumCost S P) bits≤
      2*(before+FamilyCold.budget P H V (FamilyResources.sumCost S P) bits) := by
  have h:=Nat.mul_le_mul_left V (costs_le S P hp).2.1
  unfold FamilyCold.budget FamilyRun.budget FamilyWork.budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutWitness.SupportCostRatio

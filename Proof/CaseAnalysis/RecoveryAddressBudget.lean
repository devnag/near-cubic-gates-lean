import Proof.CaseAnalysis.RecoveryAddressOriginal

/-! The whole original address expression fits the same recovery capacity
and whole-selector log already allocated by the enclosing producer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reverse_budget_cubic (count W : ℕ) (hc : count ≤ W) :
    reverseBudget count W ≤ 524288*(W+1)^3 := by
  have hm:=Nat.mul_le_mul_right (24*RecoveryBoundedSelectorLoop.capacity W+66) hc
  unfold reverseBudget RecoveryBoundedSelectorLoop.capacity at hm ⊢
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

theorem budget_quartic (count W : ℕ) (hc : count ≤ W) :
    budget count W ≤ 134217900*(W+1)^4 := by
  have hf : forwardBudget count W ≤ 67108868*(W+1)^4:=RecoveryBoundedAddress.forward_budget count count W hc hc
  have hr:=reverse_budget_cubic count W hc
  have hb : RecoveryBoundedSelectorFinish.falseBits.length ≤ 100 := by decide
  unfold budget
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

theorem budget_log (count W : ℕ) (hc : count ≤ W) :
    budget count W ≤ RecoveryBoundedSelectorFinish.logCapacity W := by
  have h:=budget_quartic count W hc
  unfold RecoveryBoundedSelectorFinish.logCapacity
  omega

theorem reset_budget_quartic (count W : ℕ) (hc : count ≤ W) :
    2*budget count W+2 ≤ 268435802*(W+1)^4 := by
  have h:=budget_quartic count W hc
  have hp : 0 < (W+1)^4 := by positivity
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressFinish

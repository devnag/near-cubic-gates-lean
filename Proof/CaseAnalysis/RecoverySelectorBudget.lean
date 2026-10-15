import Proof.CaseAnalysis.RecoverySelectorOriginalRun

/-! Recovery may allocate one fixed quartic log for a whole original field
selector. This is separate from the cubic per-head rewind log. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish
open RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reverse_budget_cubic (count W : ℕ) (hc : count ≤ W) :
    reverseBudget count W ≤ 524288*(W+1)^3 := by
  have hm:=Nat.mul_le_mul_right (24*capacity W+66) hc
  unfold reverseBudget capacity at hm ⊢
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

theorem budget_quartic (count W : ℕ) (hc : count ≤ W) :
    budget count W ≤ 268435600*(W+1)^4 := by
  have hf : forwardBudget count W ≤ 134217732*(W+1)^4 := forward_budget count count W hc hc
  have hr:=reverse_budget_cubic count W hc
  have hb : falseBits.length ≤ 100 := by decide
  unfold budget
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

def logCapacity (W : ℕ):=268435600*(W+1)^4
theorem reset_budget_quartic (count W : ℕ) (hc : count ≤ W) :
    2*budget count W+2 ≤ 536871202*(W+1)^4 := by
  have h:=budget_quartic count W hc
  have hp : 0 < (W+1)^4 := by positivity
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorFinish

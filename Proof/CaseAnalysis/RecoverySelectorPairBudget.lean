import Proof.CaseAnalysis.RecoverySelectorPairRun

/-! Both original field selectors and their actual scalar handoff remain
within one fixed quartic recovery budget. The logs are reused sequentially. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair
open RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_quartic (count acc next W : ℕ) (hc : count ≤ W) (ha : acc ≤ W) (hn : next ≤ W) :
    budget count acc next W ≤ 1100000000*(W+1)^4 := by
  have h:=RecoveryBoundedSelectorFinish.reset_budget_quartic count W hc
  unfold budget RecoveryBoundedSelectorReuse.resetBudget capacity
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair

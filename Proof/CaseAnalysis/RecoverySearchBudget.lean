import Proof.CaseAnalysis.RecoverySearchWhole
import Proof.CaseAnalysis.RecoverySearchRequest
import Proof.Amplification.RecoveryPrefixColdBudget

/-! A sufficient cubic bound in the actual payload width and description
length includes the one case query, its reset and the total prefix search. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearch
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (C payload total : Nat) :
    budget C payload total ≤ (100*C+500)*(RecoveryPrefixCold.radius payload total)^3 := by
  let r:=RecoveryPrefixCold.radius payload total
  have hr : 1 ≤ r := by dsimp [r,RecoveryPrefixCold.radius];omega
  have h1 : 1 ≤ r^3:=Nat.one_le_pow _ _ hr
  have h2 : r^2 ≤ r^3:=Nat.pow_le_pow_right hr (by decide)
  have hcap : RecoveryPrefixColdPrepare.capacity C payload total ≤ C*r^3 :=
    Nat.mul_le_mul_left C h2
  have hc : RecoveryBoundedSearchCase.coldBudget C payload total ≤
      RecoveryPrefixCold.budget C payload total+20*RecoveryPrefixColdPrepare.capacity C payload total+8 := by
    unfold RecoveryBoundedSearchCase.coldBudget RecoveryPrefixCold.budget
    omega
  have hs:=RecoveryPrefixCold.budget_bound C payload total
  change RecoveryPrefixCold.budget C payload total ≤ (40*C+200)*r^3 at hs
  change budget C payload total ≤ (100*C+500)*r^3
  unfold budget
  nlinarith

theorem request_budget_bound (payload total : Nat) :
    RecoveryBoundedSearchRequest.budget payload total ≤ 64*RecoveryPrefixCold.radius payload total := by
  simp only [RecoveryBoundedSearchRequest.budget,RecoveryPCPFormulaResumeSearchPair.framedBudget,
    RecoveryPCPFormulaResumeSearchPair.budget,RecoveryPrefixCold.radius,List.length_replicate,
    List.length_append,frame_length]
  omega

def fullBudget (C payload total : Nat):=RecoveryBoundedSearchRequest.budget payload total+
  budget C payload total+2

theorem full_budget_bound (payload total : Nat) :
    fullBudget 1073741824 payload total ≤ 1099511627776*(RecoveryPrefixCold.radius payload total)^3 := by
  let r:=RecoveryPrefixCold.radius payload total
  have hr : 1 ≤ r := by dsimp [r,RecoveryPrefixCold.radius];omega
  have h1 : 1 ≤ r^3:=Nat.one_le_pow _ _ hr
  have hl : r ≤ r^3:=Nat.le_self_pow (by decide) r
  have hs:=budget_bound 1073741824 payload total
  have hq:=request_budget_bound payload total
  change budget 1073741824 payload total ≤ (100*1073741824+500)*r^3 at hs
  change RecoveryBoundedSearchRequest.budget payload total ≤ 64*r at hq
  change fullBudget 1073741824 payload total ≤ 1099511627776*r^3
  unfold fullBudget
  omega

end NearCubicWires.RepairSource.RecoveryBoundedSearch

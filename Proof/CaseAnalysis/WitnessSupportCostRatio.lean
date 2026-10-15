import Proof.CaseAnalysis.RowsSupportFamilyCosts

/-! The actual source-selected capacity already dominates core scale.
The strengthened support stream doubles only the old family coefficient. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SupportCostRatio
open CloseoutRowsSupportStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem costs_le (S P : ℕ) (hp:FamilyResources.capacity S≤P) :
    FamilyCosts.termCost S P≤2*FamilyResources.termCost S P ∧
    FamilyCosts.sumCost S P≤2*FamilyResources.sumCost S P ∧
    FamilyCosts.totalCost S P≤2*FamilyResources.totalCost S P := by
  have hs:S≤P:=by have h:=(FamilyResources.capacity_parts S).1;omega
  have ht:FamilyCosts.termCost S P≤2*FamilyResources.termCost S P:=by
    have h:=Nat.mul_le_mul_left (10000*(S+2)) (show P+S+1≤2*(P+1) by omega)
    simpa only [FamilyCosts.termCost,FamilyResources.termCost,Nat.mul_left_comm,Nat.mul_assoc] using h
  have hu:FamilyCosts.sumCost S P≤2*FamilyResources.sumCost S P:=by
    have h:=Nat.mul_le_mul_left (1000*(S+2))
      (show FamilyCosts.termCost S P+P+1≤2*(FamilyResources.termCost S P+P+1) by omega)
    simpa only [FamilyCosts.sumCost,FamilyResources.sumCost,Nat.mul_left_comm,Nat.mul_assoc] using h
  have hv:FamilyCosts.totalCost S P≤2*FamilyResources.totalCost S P:=by
    have h:=Nat.mul_le_mul_left (100*(S+2))
      (show FamilyCosts.sumCost S P+P+1≤2*(FamilyResources.sumCost S P+P+1) by omega)
    simpa only [FamilyCosts.totalCost,FamilyResources.totalCost,Nat.mul_left_comm,Nat.mul_assoc] using h
  exact ⟨ht,hu,hv⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.SupportCostRatio

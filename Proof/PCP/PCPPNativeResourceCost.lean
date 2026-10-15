import Proof.PCP.PCPPNativeHierarchySource
import Proof.PCP.PCPSerializerCapacityBounds

/-! Fixed-degree costs of the actual measured C/F/G producer and original
query loop. The carrier is the shared measured native resource value. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceCost
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_budget (D C W : ℕ) : PCPSerializerCapacity.Power.budget D C W≤
    PCPSerializerCapacity.coefficient D C*(W+1)^(D+1) := by
  have h:=PCPSerializerCapacity.budget_bound D C W
  unfold PCPSerializerCapacity.budget at h
  omega

theorem capacity_budget (W : ℕ) : PCPPNativeCapacityCold.budget 2 16384 W≤100000000000*(W+1)^4 := by
  have h0:=power_budget 2 16384 W
  have h1:=power_budget 2 (32*16384) W
  have h2:=power_budget 3 (4096*16384) W
  norm_num [PCPSerializerCapacity.coefficient] at h0 h1 h2
  have h34 : (W+1)^3≤(W+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp : 1≤(W+1)^4 := Nat.one_le_pow _ _ (by omega)
  unfold PCPPNativeCapacityCold.budget
  norm_num
  omega

theorem count_budget (R Q s M Lq Lc : ℕ) : PCPPNativeCount.budget Q s M≤
    100*(PCPPNativeResources.W R Q s M Lq Lc+1)^2 := by
  let W:=PCPPNativeResources.W R Q s M Lq Lc
  obtain ⟨_,_,hq,hn,ht,_,_⟩:=PCPPNativeResources.bounds R Q s M Lq Lc
  have hs : s≤W := by dsimp [PCPPNativeCount.stride] at ht; omega
  have hm : M≤W := by
    dsimp [PCPPNativeCount.nativeSize,PCPPNativeCount.outputIndex] at hn
    omega
  have hi : PCPPNativeCount.outputIndex Q s M≤W := by
    dsimp [PCPPNativeCount.nativeSize] at hn
    omega
  have hprod:=Nat.mul_le_mul hq ht
  change Q*PCPPNativeCount.stride s≤W*W at hprod
  change PCPPNativeCount.budget Q s M≤100*(W+1)^2
  unfold PCPPNativeCount.budget WilliamsUnaryProduct.budget
  nlinarith

theorem envelope_budget (R Q s M Lq Lc : ℕ) :
    PCPPNativeEnvelope.budget R Q (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc≤
      64*(PCPPNativeResources.W R Q s M Lq Lc+1) := by
  obtain ⟨_,hr,hq,hn,ht,hlq,hlc⟩:=PCPPNativeResources.bounds R Q s M Lq Lc
  unfold PCPPNativeEnvelope.budget
  change _≤64*(PCPPNativeEnvelope.value R Q (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc+1)
  dsimp only [PCPPNativeResources.W] at hr hq hn ht hlq hlc
  omega

theorem query_budget (R Q s M Lq Lc : ℕ) : PCPPNativeQueryConjunction.budget R Q s M Lq Lc≤
    200000000000*(PCPPNativeResources.W R Q s M Lq Lc+1)^4 := by
  let W:=PCPPNativeResources.W R Q s M Lq Lc
  have hc:=count_budget R Q s M Lq Lc
  have he:=envelope_budget R Q s M Lq Lc
  have hb:=capacity_budget W
  obtain ⟨_,hr,hq,hn,_,_,_⟩:=PCPPNativeResources.bounds R Q s M Lq Lc
  have hqe : Q*(2*s+1)≤W := by
    dsimp [PCPPNativeCount.nativeSize,PCPPNativeCount.outputIndex,PCPPNativeCount.queryEnd,PCPPNativeCount.stride] at hn
    omega
  have hqp:=Nat.mul_le_mul_right ((W+1)^3) (show Q≤W+1 by omega)
  have hq4 : Q*(W+1)^3≤(W+1)^4 := by simpa [pow_succ,Nat.mul_comm] using hqp
  have h14 : W+1≤(W+1)^4 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0<W+1) (by decide : 1≤4))
  have h24 : (W+1)^2≤(W+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h34 : (W+1)^3≤(W+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  change PCPPNativeQueryConjunction.budget R Q s M Lq Lc≤200000000000*(W+1)^4
  unfold PCPPNativeQueryConjunction.budget PCPPNativeResourceQuery.budget PCPPNativeResources.budget
    PCPPNativeQueryCold.queryBudget PCPPNativeQueryCold.budget PCPPNativeConjunctionStart.budget
    PCPPNativeCapacityReady.G
  have htrue : PCPPNativeConjunctionStart.trueBits.length=9 := by decide
  rw [htrue]
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPNativeResourceCost

import Proof.PCP.PCPPNativeCounterCost

/-! The completed descriptor and faithful source/cache consumer has a
source-fixed degree. Framing is paid from the actual native output length. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceCost
open SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cacheDegree (a : PointwisePCPPAlgorithm) := max 2 (PCPPSourceCache.totalDegree a)
def cacheCoefficient (a : PointwisePCPPAlgorithm) := 74+55296*(a.minimumArity+1)^2+
  PCPPSourceCache.coefficient a*(2*a.minimumArity+5)^cacheDegree a

theorem descriptor_budget (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) (fuel : ℕ)
    (hlen : (c.nodes.flatMap PCPPRequestNodeSchema.native).length≤fuel) :
    PCPPNativeClauseDescriptor.budget a.minimumArity n c.size c.output.val
      (c.nodes.flatMap PCPPRequestNodeSchema.native)≤9216*(a.minimumArity+n+c.size+1)^2+2*fuel+3 := by
  have he:=PCPPNativeDescriptorBounds.entry_budget a.minimumArity n c.size
  have ht:=PCPPNativeDescriptorTail.budget_bound (PCPPNativeColdMetadata.padding a.minimumArity n c.size) c.output.val
  have hi:=c.output.isLt
  change c.output.val<c.size at hi
  have hp : PCPPNativeColdMetadata.padding a.minimumArity n c.size+c.output.val+1≤a.minimumArity+n+c.size+1 := by
    unfold PCPPNativeColdMetadata.padding PCPPNativeColdMetadata.domain
    omega
  have hsq:=Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hp 2)
  unfold PCPPNativeClauseDescriptor.budget
  omega

theorem cache_parameter (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    PCPPRequestRuntime.sourceParameter (PCPPRequestBoundary.request a c).circuit≤
      (2*a.minimumArity+5)*(n+c.size+1) := by
  unfold PCPPRequestRuntime.sourceParameter
  rw [PCPPRequestBoundary.request_size]
  change PCPPRequestBoundary.domain a n+max c.size (PCPPRequestBoundary.domain a n)+5≤_
  have hd : PCPPRequestBoundary.domain a n≤n+a.minimumArity := by unfold PCPPRequestBoundary.domain; omega
  have hm : max c.size (PCPPRequestBoundary.domain a n)≤c.size+n+a.minimumArity := by omega
  nlinarith

theorem source_budget (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) (fuel : ℕ)
    (hlen : (c.nodes.flatMap PCPPRequestNodeSchema.native).length≤fuel) :
    PCPPNativeClauseDescriptorConsumer.sourceBudget a c fuel≤
      48*fuel+cacheCoefficient a*(n+c.size+1)^cacheDegree a := by
  let S:=n+c.size+1
  have hs : 1≤S := by dsimp [S]; omega
  have hd : 2≤cacheDegree a := Nat.le_max_left _ _
  have hc : PCPPSourceCache.totalDegree a≤cacheDegree a := Nat.le_max_right _ _
  have ht:=descriptor_budget a c fuel hlen
  have hp : a.minimumArity+n+c.size+1≤(a.minimumArity+1)*S := by dsimp [S]; nlinarith
  have hsq:=Nat.pow_le_pow_left hp 2
  rw [mul_pow] at hsq
  have hpow : S^2≤S^cacheDegree a := Nat.pow_le_pow_right hs hd
  have hhead:=Nat.mul_le_mul_left ((a.minimumArity+1)^2) hpow
  have hsrc:=(Nat.pow_le_pow_left (cache_parameter a c) (PCPPSourceCache.totalDegree a)).trans
    (Nat.pow_le_pow_right (by positivity) hc)
  rw [mul_pow] at hsrc
  have hcache:=Nat.mul_le_mul_left (PCPPSourceCache.coefficient a) hsrc
  have hone : 1≤S^cacheDegree a := Nat.one_le_pow _ _ hs
  unfold PCPPNativeClauseDescriptorConsumer.sourceBudget PCPPNativeSource.budget
    PCPPNativeClauseDescriptorConsumer.budget PCPPSourceCache.totalBudget cacheCoefficient
  dsimp only [S] at *
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPNativeResourceCost

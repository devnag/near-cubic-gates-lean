import SourceAdapters.Proximity.TrimHonestCompile

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the full paid ordinary honest-proof restriction,
discharging the interface from source algorithms alone. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

theorem honestRestriction_join : HonestRestriction := by
  intro q V proofSize honest a hr hsource
  obtain ⟨K, e, ⟨P⟩⟩ := hsource
  obtain ⟨A, D, hA, H⟩ := HonestFullAllocation.sufficient_allocation V proofSize honest K e a P hr
  exact HonestAllocation.polynomial (preparedHonestInput V) (preparedHonestOutput V proofSize honest)
    (SourceCallee.callee V proofSize honest _ P) A D
    (fun p => HonestFullAllocation.cost V proofSize K e a p
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p))
    (HonestFullAllocation.allocated_cost_bounded V proofSize honest K e a P hr A D)
    (allocatedWordFunction V proofSize honest K e a P A D hA H)

end NearCubicGates.Adapters.Proximity.TrimHonest

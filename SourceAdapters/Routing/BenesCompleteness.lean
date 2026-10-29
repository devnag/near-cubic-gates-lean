import SourceAdapters.Routing.BenesFlatten

/-! All-size completeness on the exact dimension schedule and path. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.Completeness

/-- Every permutation has coherent switch settings on the `2*k-1` stages
of the routing interface, including the single-switch case `k=1`. -/
theorem benesCompleteness : BenesCompleteness := by
  intro k hk π
  obtain ⟨C, hC, _⟩ := BenesRecursive.complete k hk π
  refine ⟨C.settings, C.coherent, ?_⟩
  intro x
  rw [C.path_eq_perm, hC]

end NearCubicGates.Adapters.Routing.Completeness

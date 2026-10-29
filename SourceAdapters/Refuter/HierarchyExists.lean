import SourceAdapters.Refuter.Hierarchy
import SourceAdapters.Machine.CappedRunProof

/-!
# `HierarchyRecurrence` at every admissible clock (input 7, internal join of `Assembly.lean`)

The hierarchy half of `clw20_theorem1_13_of_parts` (`Witnesses.lean`): for every time-constructible `T` with
`n ≤ T(n) ≤ 2^{poly(n)}` there is a hierarchy verifier `H : OrdinaryHierarchy T` (`cor:framed-refuter`,
: time bound and witness length `c(T(N)+1)`) whose language obeys the exact recurrence of proof of `cor:framed-refuter` for every promised weak machine at all large lengths. The capped run is the join
`CappedMachineRun` (`Joins/CappedRun.lean`), discharged by `Machine.Capped.cappedMachineRun`.
Only `N ≤ T(N)` is used from the clock range ("The argument uses only `N ≤ T(N)`, so it
includes linear clocks").
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.Bindings.CLW20Theorem113

set_option autoImplicit false

/-- **The hierarchy half of input 7.** -/
theorem hierarchy_exists :
    ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → ∃ H : OrdinaryHierarchy T, HierarchyRecurrence T H :=
  Clock.hierarchyRecurrence_of_capped NearCubicGates.Adapters.Machine.Capped.cappedMachineRun

/-- The consumer `CLW20_Theorem1_13` from the refuter half alone (`RefuterRealization`). -/
theorem clw20_theorem1_13_of_realization
    (hR : ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → RefuterRealization T) : CLW20_Theorem1_13 :=
  clw20_theorem1_13_of_parts fun T hT hC => by
    obtain ⟨H, hH⟩ := hierarchy_exists T hT hC
    exact ⟨H, hH, hR T hT hC⟩

end NearCubicGates.Adapters.Refuter

import SourceAdapters.Code.DistinctRecordsSpec

set_option autoImplicit false
namespace NearCubicGates.Adapters.Code.DistinctRecords
open NearCubicGates.Close.Cells

theorem Registers.separations (r : Registers) (h : r.Valid) :
    c0 ∉ [r.current, r.previous, r.started, r.count] ∧
    vJ ∉ [r.current, r.previous, r.started, r.count] ∧
    r.current ≠ r.previous ∧ r.current ≠ r.started ∧ r.current ≠ r.count ∧
    r.previous ≠ r.started ∧ r.previous ≠ r.count ∧ r.started ≠ r.count := by
  simp [Registers.Valid, scratch] at h ⊢
  tauto

end NearCubicGates.Adapters.Code.DistinctRecords

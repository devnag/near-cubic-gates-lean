import SourceAdapters.Proximity.TrimRenderFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the checked natural-field printer preserves rendering data. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells

theorem printed_frame {a b : DS VV MM} {word : List Bool}
    (h : SourcePrinting.Printed a b word) : RenderFrame SourcePrinting.scratch a b := by
  have hr := h.rest_eq
  simp only [SourcePrinting.rest, Prod.mk.injEq] at hr
  exact ⟨hr.2.1, fun m _ _ => congrFun hr.2.2.1 m, hr.1,
    hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, h.vars⟩

theorem printed_cursor {a b : DS VV MM} {word : List Bool}
    (h : SourcePrinting.Printed a b word) (m : Fin MM) : b.rc m = a.rc m := by
  have hr := h.rest_eq
  simp only [SourcePrinting.rest, Prod.mk.injEq] at hr
  exact congrFun hr.2.2.1 m

end NearCubicGates.Adapters.Proximity.Trim

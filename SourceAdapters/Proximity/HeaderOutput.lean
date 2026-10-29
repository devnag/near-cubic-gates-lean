import SourceAdapters.Proximity.HeaderParameters

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the exact arity and random-bit headers of the flat
trimming request, printed by the paid natWord writer. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceHeader

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

def printHeader : Script := LegacyOutput.fieldsFrom [arityReg, totalRandomReg]

theorem print_header (C : Ctx) (a : State) (hc : Cst a) (n r : ℕ)
    (hn : a.env arityReg = n) (hr : a.env totalRandomReg = r) (hW : 2 ≤ C.Wd)
    (hnW : natBitLength n + 2 < 2 ^ C.Wd) (hrW : natBitLength r + 2 < 2 ^ C.Wd) :
    Hs C printHeader a (40 * natBitLength n + 40 * natBitLength r + 87)
      (fun b => LegacyOutput.Printed a b (natWord n ++ natWord r)) := by
  have e := LegacyOutput.fields_from C [arityReg, totalRandomReg] a hc hW (by decide) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa [hn] using hnW
    · simpa [hr] using hrW)
  simp only [LegacyOutput.fieldsCost, LegacyOutput.fieldsWord, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, hn, hr] at e
  exact e.mono (by omega) (fun _ h => h)

end NearCubicGates.Adapters.Proximity.SourceHeader

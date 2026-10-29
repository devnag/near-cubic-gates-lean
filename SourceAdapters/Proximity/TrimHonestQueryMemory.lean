import SourceAdapters.Proximity.TrimHonestQueryFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": query reads and answer writes preserve both actual
finite oracle stores, including their exact lengths and default semantics. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

namespace OracleReady
variable {n N : ℕ} {C : Ctx} {input : BitInput n} {proof : BitInput N} {a : DS VV MM}
theorem advance_query (h : OracleReady C input proof a) :
    OracleReady C input proof (a.adv queryStore) := by
  refine ⟨h.input_ram, h.input_len, ?_, h.input_width, h.proof_ram, h.proof_len, ?_, h.proof_width⟩
  · simpa [DS.adv, inputStore, queryStore] using h.input_cursor
  · simpa [DS.adv, proofStore, queryStore] using h.proof_cursor
theorem put_answer (h : OracleReady C input proof a) (v : ℕ) :
    OracleReady C input proof (a.put answerStore v) := by
  refine ⟨?_, h.input_len, ?_, h.input_width, ?_, h.proof_len, ?_, h.proof_width⟩
  · simpa [DS.put, inputStore, answerStore] using h.input_ram
  · simpa [DS.put, inputStore, answerStore] using h.input_cursor
  · simpa [DS.put, proofStore, answerStore] using h.proof_ram
  · simpa [DS.put, proofStore, answerStore] using h.proof_cursor
end OracleReady

def queryReadTemps : List (Fin VV) := [queryTagReg, addressReg]
def afterQueryRead (a : DS VV MM) (reg : Fin VV) (v : ℕ) : DS VV MM := (a.set reg v).adv queryStore

theorem read_query_head {C : Ctx} (a : DS VV MM) (reg : Fin VV) (v : ℕ) (tail : List ℕ)
    (h : (a.ram queryStore).drop (a.rc queryStore) = v :: tail) :
    Ex C (.op (.rdM queryStore reg)) a (afterQueryRead a reg v) 1 ∧
      ((afterQueryRead a reg v).ram queryStore).drop ((afterQueryRead a reg v).rc queryStore) = tail := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_cons] at hl
  have hv : (a.ram queryStore).getD (a.rc queryStore) 0 = v := fld_of_drop h
  constructor
  · simpa only [afterQueryRead, hv] using Ex.op (OpEx.rdM (C := C) queryStore reg a (by omega))
  · change (a.ram queryStore).drop (a.rc queryStore + 1) = tail
    rw [← List.drop_drop, h]
    rfl

theorem after_query_frame (a : DS VV MM) (reg : Fin VV) (v : ℕ) (hr : reg ∈ queryReadTemps) :
    QueryFrame queryReadTemps a (afterQueryRead a reg v) :=
  (QueryFrame.set _ _ _ _ hr).trans (QueryFrame.advance _ _)

end NearCubicGates.Adapters.Proximity.TrimHonest

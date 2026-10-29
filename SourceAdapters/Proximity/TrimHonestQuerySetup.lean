import SourceAdapters.Proximity.TrimHonestQueryLoop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": both reused row cursors are physically rewound before
answer generation, and the protected answer index is initialized. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def answerSetup : St VV MM := .seq (.op (.rwM queryStore))
  (.seq (.op (.rwM answerStore)) (.op (.zero answerIndex)))
def answerInitial (a : DS VV MM) : DS VV MM :=
  ((a.rew queryStore).rew answerStore).set answerIndex 0

theorem answer_setup (a : DS VV MM) :
    Ex C answerSetup a (answerInitial a) (a.rc queryStore + a.rc answerStore + 5) := by
  have e1 := Ex.op (OpEx.rwM (C := C) queryStore a)
  have e2 := Ex.op (OpEx.rwM (C := C) answerStore (a.rew queryStore))
  have e3 := Ex.op (OpEx.zero (C := C) answerIndex ((a.rew queryStore).rew answerStore))
  have hr : (a.rew queryStore).rc answerStore = a.rc answerStore := by
    simp [DS.rew, queryStore, answerStore]
  rw [hr] at e2
  have he := Ex.seq e1 (Ex.seq e2 e3)
  convert he using 1
  · rfl
  · rfl
  · omega

private theorem rewind_frame (a : DS VV MM) (m : Fin MM) (hm : m ∈ queryCursors) :
    QueryFrame answerLoopTemps a (a.rew m) := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  intro j hj
  have hn : j ≠ m := by intro h; apply hj; simpa [h] using hm
  simp [DS.rew, hn]

theorem answer_initial_frame (a : DS VV MM) : QueryFrame answerLoopTemps a (answerInitial a) :=
  (rewind_frame a queryStore (by decide)).trans
    ((rewind_frame _ answerStore (by decide)).trans
      (QueryFrame.set answerLoopTemps _ answerIndex 0 (by simp [answerLoopTemps])))

theorem OracleReady.answer_initial {n N : ℕ} {input : BitInput n} {proof : BitInput N}
    {a : DS VV MM} (h : OracleReady C input proof a) :
    OracleReady C input proof (answerInitial a) := by
  have hr : OracleReady C input proof ((a.rew queryStore).rew answerStore) := by
    refine ⟨h.input_ram, h.input_len, ?_, h.input_width, h.proof_ram, h.proof_len, ?_, h.proof_width⟩
    · simpa [DS.rew, inputStore, queryStore, answerStore] using h.input_cursor
    · simpa [DS.rew, proofStore, queryStore, answerStore] using h.proof_cursor
  exact hr.set answerIndex 0 (by decide) (by decide)

end NearCubicGates.Adapters.Proximity.TrimHonest

import SourceAdapters.Proximity.TrimRenderLoop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid rewind and loop-counter initialization. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
variable {C : Ctx}

def renderSetup : St VV MM := .seq (.op (.rwM sN)) (.op (.zero renderIndex))
def renderInitial (a : DS VV MM) : DS VV MM := (a.rew sN).set renderIndex 0

theorem render_setup (a : DS VV MM) :
    Ex C renderSetup a (renderInitial a) (a.rc sN + 3) := by
  simpa only [renderSetup, renderInitial, Nat.add_assoc] using
    Ex.seq (Ex.op (OpEx.rwM (C := C) sN a)) (Ex.op (OpEx.zero renderIndex (a.rew sN)))

theorem render_initial_frame (a : DS VV MM) : RenderFrame renderStepTemps a (renderInitial a) := by
  have hf : RenderFrame renderStepTemps a (a.rew sN) := by
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    intro m hm _
    simp [DS.rew, hm]
  exact hf.trans (RenderFrame.set renderStepTemps _ renderIndex 0 (by simp [renderStepTemps]))

end NearCubicGates.Adapters.Proximity.Trim

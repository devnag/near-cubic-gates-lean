import Proof.Amplification.RecoveryMarkerClauseLoad

/-! Three already present framed fields retain the marker payload,
committed assignment and count. Copying them uses two distinct reset
buffers; the marker replay needs no additional natural-number bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerSave
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def target : Fin 3→Fin 57 := ![54,55,25]
def slots (which : Fin 3) : Fin 4→Fin 57 := ![24,target which,22,51]
theorem slots_injective (which : Fin 3) : Function.Injective (slots which) := by fin_cases which <;> decide
noncomputable def machine (which : Fin 3) := RecoveryFocus.machine (slots which) RecoveryRootRound.copyMachine
def refreshed (x : State) : State :=
  let data := {x.inner.data with capacity:=max x.inner.data.capacity (2*x.width+1)}
  let inner := {x.inner with data:=data}
  let outer := {x.outer with capacity:=max x.outer.capacity (4*x.width+3)}
  ⟨inner,outer⟩
def stored (x : State) (which : Fin 3) : State :=
  if h : which.val=2 then
    {x with inner:={x.inner with data:={x.inner.data with fields:=Function.update x.inner.data.fields 1 (x.inner.data.fields 0)}}}
  else
    {x with outer:={x.outer with fields:=Function.update x.outer.fields ⟨which.val+1,by omega⟩ (x.inner.data.fields 0)}}
def saved (x : State) (which : Fin 3) := stored (refreshed x) which

theorem field_tapes (s : RecoveryClauseState.State) (which : Fin 3) (word : List Bool) :
    ({s with fields:=Function.update s.fields which word} : RecoveryClauseState.State).tapes=
      Function.update s.tapes (RecoveryClauseState.savedSlot which) word := by
  change Fin.addCases (m:=24) (n:=4) (motive:=fun _=>List Bool) s.core
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) (Function.update s.fields which word) (fun _=>[s.result]))=_
  rw [bank_update_left,bank_update_right]
  rfl

theorem refreshed_tapes (x : State) : (refreshed x).tapes=
    Function.update (Function.update x.tapes 22 (List.replicate (max x.inner.data.capacity (2*x.width+1)) false))
      51 (List.replicate (max x.outer.capacity (4*x.width+3)) false) := by
  have hi := RecoveryRawView.reset_core_tapes x.inner.data (max x.inner.data.capacity (2*x.width+1))
  have ho := RecoveryRawView.reset_core_tapes x.outer (max x.outer.capacity (4*x.width+3))
  change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
      ({x.inner.data with capacity:=max x.inner.data.capacity (2*x.width+1)} : RecoveryClauseState.State).tapes
      (fun _=>[x.inner.present]))
    ({x.outer with capacity:=max x.outer.capacity (4*x.width+3)} : RecoveryClauseState.State).tapes=_
  rw [hi,ho,bank_update_left,bank_update_left,bank_update_right]
  change Function.update (Function.update x.tapes 51 _) 22 _=Function.update (Function.update x.tapes 22 _) 51 _
  exact Function.update_comm (by decide) _ _ _

theorem stored_tapes (x : State) (which : Fin 3) :
    (stored x which).tapes=Function.update x.tapes (target which) (x.inner.data.fields 0) := by
  fin_cases which
  · change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool) x.inner.tapes
      ({x.outer with fields:=Function.update x.outer.fields 1 (x.inner.data.fields 0)} : RecoveryClauseState.State).tapes=_
    rw [field_tapes,bank_update_right]
    rfl
  · change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool) x.inner.tapes
      ({x.outer with fields:=Function.update x.outer.fields 2 (x.inner.data.fields 0)} : RecoveryClauseState.State).tapes=_
    rw [field_tapes,bank_update_right]
    rfl
  · change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
        ({x.inner.data with fields:=Function.update x.inner.data.fields 1 (x.inner.data.fields 0)} : RecoveryClauseState.State).tapes
        (fun _=>[x.inner.present])) x.outer.tapes=_
    rw [field_tapes,bank_update_left,bank_update_left]
    rfl

theorem saved_tapes (x : State) (which : Fin 3) :
    (saved x which).tapes=Function.update
      (Function.update (Function.update x.tapes 22 (List.replicate (max x.inner.data.capacity (2*x.width+1)) false))
        51 (List.replicate (max x.outer.capacity (4*x.width+3)) false))
      (target which) (x.inner.data.fields 0) := by
  rw [saved,stored_tapes,refreshed_tapes]
  rfl

theorem saved_width (x : State) (which : Fin 3) : (saved x which).width=x.width := by
  unfold saved stored
  split <;> rfl

theorem saved_valid (x : State) (which : Fin 3) (hx : x.Valid) : (saved x which).Valid := by
  have hb : (x.inner.data.fields 0).length ≤ 2*x.width+1 := hx.1.2 0
  unfold saved stored
  split
  · refine ⟨⟨hx.1.1,?_⟩,hx.2.1,hx.2.2⟩
    intro i
    by_cases hi : i=1
    · subst i; exact hb
    · change (Function.update x.inner.data.fields 1 (x.inner.data.fields 0) i).length ≤ _
      rw [Function.update_of_ne hi]
      exact hx.1.2 i
  · refine ⟨hx.1,⟨hx.2.1.1,?_⟩,hx.2.2⟩
    intro i
    by_cases hi : i=⟨which.val+1,by omega⟩
    · subst i
      simp only [refreshed,Function.update_self]
      rw [hx.2.2]
      exact hb
    · change (Function.update x.outer.fields ⟨which.val+1,by omega⟩ (x.inner.data.fields 0) i).length ≤ _
      rw [Function.update_of_ne hi]
      exact hx.2.1.2 i

end NearCubicWires.RepairOrdinary.RecoveryMarkerSave

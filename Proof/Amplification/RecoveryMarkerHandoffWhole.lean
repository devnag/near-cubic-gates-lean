import Proof.Amplification.RecoveryMarkerFields

/-! All three actual copies from saved marker fields into the reused
flat/nested checker bank, including the two paid call returns. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tailMachine := Composition.machine (copyMachine 1) (copyMachine 2)
noncomputable def machine := Composition.machine (copyMachine 0) tailMachine
def output (x : CheckState) (words : Fin 3→List Bool) := stored (stored (stored x 0 (words 0)) 1 (words 1)) 2 (words 2)

theorem handoff_run (marker : MarkerState) (x : CheckState) (width : Nat) (words : Fin 3→List Bool)
    (hw : ∀ j,(words j).length=width)
    (hs : ∀ j,marker.tapes (RecoveryMarkerSave.target j)=frame (words j))
    (hb : ∀ j,(oldWord x j).length ≤ width)
    (hc : 2*width+1 ≤ x.inner.copyCapacity)
    (hz : 4*width+3 ≤ x.inner.base.state.capacity) :
    ∃ r,runFrom machine (24*width+26) (cfg marker x machine.start)=some r ∧
      r.final=cfg marker (output x words) r.final.control ∧ r.steps=24*width+26 := by
  let x1 := stored x 0 (words 0)
  let x2 := stored x1 1 (words 1)
  obtain ⟨a,ha,haf,hat⟩ := copy_run marker x 0 (words 0) (hs 0)
    (by rw [hw]; exact hb 0) (by rw [hw]; exact hc) (by rw [hw]; exact hz)
  obtain ⟨b,hb0,hbf,hbt⟩ := copy_run marker x1 1 (words 1) (hs 1)
    (by change (oldWord x 1).length ≤ _; rw [hw]; exact hb 1)
    (by change 2*(words 1).length+1 ≤ x.inner.copyCapacity; rw [hw]; exact hc)
    (by change 4*(words 1).length+3 ≤ x.inner.base.state.capacity; rw [hw]; exact hz)
  obtain ⟨c,hc0,hcf,hct⟩ := copy_run marker x2 2 (words 2) (hs 2)
    (by change (oldWord x 2).length ≤ _; rw [hw]; exact hb 2)
    (by change 2*(words 2).length+1 ≤ x.inner.copyCapacity; rw [hw]; exact hc)
    (by change 4*(words 2).length+3 ≤ x.inner.base.state.capacity; rw [hw]; exact hz)
  rw [hw] at ha hat hb0 hbt hc0 hct
  have hnext2 : Composition.restart b.final (copyMachine 2).start=cfg marker x2 (copyMachine 2).start := by
    rw [hbf]; rfl
  rw [←hnext2] at hc0
  have htail := Composition.run_join (copyMachine 1) (copyMachine 2)
    (8*width+8) (8*width+8) _ b c hb0 hc0
  let bc := Composition.joinedReceipt b c
  have hbct : bc.steps=16*width+17 := by change b.steps+1+c.steps=_; rw [hbt,hct]; omega
  have hbcf : bc.final=cfg marker (output x words) bc.final.control := by
    apply configuration_ext
    · rfl
    · change c.final.heads=heads (output x words); rw [hcf]; rfl
    · change c.final.tapes=tapes marker (output x words); rw [hcf]; rfl
  have hnext1 : Composition.restart a.final tailMachine.start=cfg marker x1 tailMachine.start := by
    rw [haf]; rfl
  have hb0' : runFrom tailMachine (16*width+17) (Composition.restart a.final tailMachine.start)=some bc := by
    rw [hnext1]
    rw [show 8*width+8+1+(8*width+8)=16*width+17 by omega] at htail
    exact htail
  have h := Composition.run_join (copyMachine 0) tailMachine (8*width+8) (16*width+17) _ a bc ha hb0'
  refine ⟨Composition.joinedReceipt a bc,?_,?_,?_⟩
  · rw [show 8*width+8+1+(16*width+17)=24*width+26 by omega] at h
    exact h
  · apply configuration_ext
    · rfl
    · change bc.final.heads=heads (output x words); rw [hbcf]; rfl
    · change bc.final.tapes=tapes marker (output x words); rw [hbcf]; rfl
  · change a.steps+1+bc.steps=_
    rw [hat,hbct]
    omega

end NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff

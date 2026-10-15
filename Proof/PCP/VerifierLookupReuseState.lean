import Proof.PCP.VerifierLookupReuseTags

/-! A successful transition promotes its physically returned next-state
field into the retained current-state tape, restoring both source and j heads. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def promoteSlots : Fin 3→Fin 21 := ![11,6,5]
noncomputable def promoteProgram := RecoveryFocus.machine promoteSlots LookupRetainField.machine

theorem promote_place (q : Fin 10) (d : Store) (bits : List Bool) :
    RecoveryFocus.config promoteSlots (cfg q d).heads (cfg q d).tapes
      (LookupRetainField.cfg q d.nextState 0 (frame bits) d.j)=cfg q {d with state:=bits} := by
  apply TransitionEvent.focused_eq promoteSlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 1 rfl) | rfl

theorem promote_run (d : Store) (bits : List Bool) (hn : d.nextState=frame bits)
    (hl : bits.length=d.j) (hs : d.state.length≤d.j) :
    ∃ r,runFrom promoteProgram (7*d.j+5) (cfg promoteProgram.start d)=some r ∧
      r.final=cfg r.final.control {d with state:=bits} ∧ r.steps=7*d.j+5 := by
  have hb : (frame d.state).length≤2*bits.length+1 := by simp only [frame_length]; omega
  obtain ⟨base,hbase,hbf,hbs⟩ := LookupRetainField.field_run [] bits [false] (frame d.state) hb
  have hsource : []++Streaming.marks bits++[false]=d.nextState := by
    rw [hn]
    simpa only [List.nil_append,RepairOrdinary.frame,List.append_nil] using (Streaming.frame_append bits []).symm
  rw [hsource,List.length_nil,hl] at hbase hbf
  rw [hl] at hbs
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config promoteSlots (by decide) LookupRetainField.machine
    (cfg LookupRetainField.machine.start d).heads (cfg LookupRetainField.machine.start d).tapes _ _ base hbase
  have hi := promote_place LookupRetainField.machine.start d d.state
  rw [show ({d with state:=d.state} : Store)=d from rfl] at hi
  rw [hi] at hr
  have ho : RecoveryFocus.config promoteSlots (cfg LookupRetainField.machine.start d).heads
      (cfg LookupRetainField.machine.start d).tapes base.final=cfg (9 : Fin 10) {d with state:=bits} := by
    rw [hbf]
    exact promote_place 9 d bits
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans hbs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime

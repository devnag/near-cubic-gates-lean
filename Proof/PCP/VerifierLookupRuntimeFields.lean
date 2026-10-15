import Proof.PCP.VerifierLookupRuntimeReaders

/-! The selected next-state and complete action-tag fields are physically
copied from the current code cursor with the retained j and produced4t tapes. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots (tags : Bool) : Fin 3→Fin 21 := if tags then tagsSlots else nextSlots
def fieldWidth (d : Store) (tags : Bool) : ℕ := if tags then 4*d.t else d.j
def fieldBacking (d : Store) (tags : Bool) : List Bool := if tags then d.tags else d.nextState
def fieldOut (d : Store) (tags : Bool) (pos : ℕ) (target : List Bool) : Store :=
  if tags then {d with codePos:=pos,tags:=target} else {d with codePos:=pos,nextState:=target}
noncomputable def fieldProgram (tags : Bool) := RecoveryFocus.machine (fieldSlots tags) FieldMachine.machine

theorem field_place (tags : Bool) (q : Fin 6) (d : Store) (pos : ℕ) (target : List Bool) :
    RecoveryFocus.config (fieldSlots tags) (cfg q d).heads (cfg q d).tapes
      (LookupRetainField.cfg q (frame d.code) pos target (fieldWidth d tags))=
      cfg q (fieldOut d tags pos target) := by
  cases tags
  all_goals apply TransitionEvent.focused_eq _ (by decide) (cfg q d)
  all_goals first
    | rfl
    | (intro z; fin_cases z <;> rfl)
    | (intro z h; fin_cases z <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl) | rfl)

theorem field_run (tags : Bool) (d : Store) (pre bits tail : List Bool)
    (hs : frame d.code=pre++Streaming.marks bits++tail) (hp : d.codePos=pre.length)
    (hl : bits.length=fieldWidth d tags) (hb : (fieldBacking d tags).length≤2*(fieldWidth d tags)+1) :
    ∃ r,runFrom (fieldProgram tags) (4*(fieldWidth d tags)+2) (cfg (fieldProgram tags).start d)=some r ∧
      r.final=cfg r.final.control (fieldOut d tags (d.codePos+2*bits.length) (frame bits)) ∧
      r.steps=4*(fieldWidth d tags)+2 := by
  obtain ⟨base,hbase,hbf,hbs,_⟩ := FieldMachine.field_run pre bits tail (fieldBacking d tags) (by omega)
  rw [←hs,←hp,hl] at hbase hbf
  rw [hl] at hbs
  have hiLocal : FieldMachine.scan 0 (frame d.code) d.codePos (fieldWidth d tags) 0 [] (fieldBacking d tags)=
      LookupRetainField.cfg (0 : Fin 6) (frame d.code) d.codePos (fieldBacking d tags) (fieldWidth d tags) := by
    apply configuration_ext
    · rfl
    · rfl
    · simp [FieldMachine.scan,LookupRetainField.cfg,StablePartition.Workspace.overlay]
  rw [hiLocal] at hbase
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config (fieldSlots tags) (by cases tags <;> decide) FieldMachine.machine
    (cfg (0 : Fin 6) d).heads (cfg (0 : Fin 6) d).tapes _ _ base hbase
  have hi := field_place tags 0 d d.codePos (fieldBacking d tags)
  have he : fieldOut d tags d.codePos (fieldBacking d tags)=d := by cases tags <;> rfl
  rw [he] at hi
  rw [hi] at hr
  have ho : RecoveryFocus.config (fieldSlots tags) (cfg (0 : Fin 6) d).heads (cfg (0 : Fin 6) d).tapes base.final=
      cfg (4 : Fin 6) (fieldOut d tags (d.codePos+2*bits.length) (frame bits)) := by
    rw [hbf,hl]
    exact field_place tags 4 d _ (frame bits)
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans hbs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime

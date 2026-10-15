import Proof.PCP.VerifierLookupTerminalFlags

/-! The transition loop checks literal witness markers before a lookup.
Short fields halt at failure control 5. Successful fields are copied and
then their exact source cursor is physically restored for the same claim. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime.ClaimGuard
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RecoveryFocus.machine claimedSlots FieldMachine.machine

theorem place (q : Fin 6) (d : Store) (pos : ℕ) (target : List Bool) :
    RecoveryFocus.config claimedSlots (cfg q d).heads (cfg q d).tapes
      (LookupRetainField.cappedCfg q d.scans pos target d.t d.code.length)=
      cfg q {d with scanPos:=pos,scanCopy:=target} := by
  apply TransitionEvent.focused_eq claimedSlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 1 rfl) | rfl

theorem initial_field (source backing : List Bool) (pos width : ℕ) :
    FieldMachine.scan 0 source pos width 0 [] backing=
      LookupRetainField.cfg 0 source pos backing width := by
  apply configuration_ext
  · rfl
  · rfl
  · simp [FieldMachine.scan,LookupRetainField.cfg,StablePartition.Workspace.overlay]

theorem full_run (d : Store) (pre bits tail : List Bool)
    (hs : d.scans=pre++Streaming.marks bits++tail) (hp : d.scanPos=pre.length)
    (hl : bits.length=d.t) (hb : d.scanCopy.length≤2*d.t+1) :
    ∃ r,runFrom machine (4*d.t+2) (cfg machine.start d)=some r ∧
      r.final=cfg (4 : Fin 6) {d with scanPos:=d.scanPos+2*d.t,scanCopy:=frame bits} ∧ r.steps=4*d.t+2 := by
  obtain ⟨base,hbase,hbf,hbs,_⟩ := FieldMachine.field_run pre bits tail d.scanCopy (by omega)
  rw [initial_field,←hs,←hp,hl] at hbase
  rw [←hs,←hp,hl] at hbf
  rw [hl] at hbs
  obtain ⟨padded,hpad,hpf,hps,_⟩ := ZeroPadding.run_config FieldMachine.machine (![0,0,d.code.length+2] : Fin 3→ℕ) _ _ base hbase
  rw [LookupRetainField.pad_cfg] at hpad
  have hpo : padded.final=LookupRetainField.cappedCfg (4 : Fin 6) d.scans (d.scanPos+2*d.t) (frame bits) d.t d.code.length := by
    rw [hpf,hbf]
    exact LookupRetainField.pad_cfg 4 d.scans _ (frame bits) d.t d.code.length
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config claimedSlots (by decide) FieldMachine.machine
    (cfg (0 : Fin 6) d).heads (cfg (0 : Fin 6) d).tapes _ _ padded hpad
  have hi := place 0 d d.scanPos d.scanCopy
  rw [show ({d with scanPos:=d.scanPos,scanCopy:=d.scanCopy} : Store)=d from rfl] at hi
  rw [hi] at hr
  refine ⟨r,hr,?_,hrs.trans (hps.trans hbs)⟩
  rw [hrf,hpo]
  exact place 4 d _ (frame bits)

theorem short_run (d : Store) (pre bits : List Bool)
    (hs : d.scans=pre++frame bits) (hp : d.scanPos=pre.length)
    (hl : bits.length<d.t) (hb : d.scanCopy.length≤2*d.t+1) :
    ∃ r,runFrom machine (4*d.t+2) (cfg machine.start d)=some r ∧
      r.final.control=(5 : Fin 6) ∧ r.steps≤4*d.t+2 := by
  obtain ⟨base,hbase,hbf,hbs,_⟩ := FieldMachine.field_reject_run pre bits d.scanCopy d.t hl hb
  rw [initial_field,←hs,←hp] at hbase
  obtain ⟨padded,hpad,hpf,hps,_⟩ := ZeroPadding.run_config FieldMachine.machine (![0,0,d.code.length+2] : Fin 3→ℕ) _ _ base hbase
  rw [LookupRetainField.pad_cfg] at hpad
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config claimedSlots (by decide) FieldMachine.machine
    (cfg (0 : Fin 6) d).heads (cfg (0 : Fin 6) d).tapes _ _ padded hpad
  have hi := place 0 d d.scanPos d.scanCopy
  rw [show ({d with scanPos:=d.scanPos,scanCopy:=d.scanCopy} : Store)=d from rfl] at hi
  rw [hi] at hr
  have htime : 2*bits.length+1≤4*d.t+2 := by omega
  have hm := runFrom_moreFuel machine _ (4*d.t+2-(2*bits.length+1)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r,hm,?_,by rw [hrs,hps,hbs]; omega⟩
  rw [hrf,hpf,hbf]
  rfl

def returnSlots : Fin 2→Fin 21 := ![7,1]
noncomputable def returnProgram := RecoveryFocus.machine returnSlots (LookupWalk.machine .left)

theorem return_place (q : Fin 4) (d : Store) (pos : ℕ) :
    RecoveryFocus.config returnSlots (cfg q d).heads (cfg q d).tapes
      (LookupWalk.cappedCfg q d.scans pos d.code.length d.t 1)=cfg q {d with scanPos:=pos} := by
  apply TransitionEvent.focused_eq returnSlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl
  · intro i _; rfl

theorem return_run (d : Store) :
    ∃ r,runFrom returnProgram (3*d.t+2) (cfg returnProgram.start d)=some r ∧
      r.final=cfg (3 : Fin 4) {d with scanPos:=d.scanPos-2*d.t} ∧ r.steps=3*d.t+2 := by
  obtain ⟨base,hbase,hbf,hbs⟩ := LookupWalk.capped_walk_run .left d.scans d.scanPos d.code.length d.t
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config returnSlots (by decide) (LookupWalk.machine .left)
    (cfg (0 : Fin 4) d).heads (cfg (0 : Fin 4) d).tapes _ _ base hbase
  have hi := return_place 0 d d.scanPos
  rw [show ({d with scanPos:=d.scanPos} : Store)=d from rfl] at hi
  rw [hi] at hr
  refine ⟨r,hr,?_,hrs.trans hbs⟩
  rw [hrf,hbf]
  exact return_place 3 d _

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime.ClaimGuard

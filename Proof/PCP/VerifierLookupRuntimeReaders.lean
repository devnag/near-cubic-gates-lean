import Proof.PCP.VerifierLookupRuntimeNavigation

/-! The retained witness field and selected scalar code fields are read by
actual machines on the common lookup store. No source suffix is installed. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots (i : Fin 3) : Fin 2 → Fin 21 := ![0,⟨8+i.val,by omega⟩]
def scalar (d : Store) : Fin 3 → Bool := ![d.halt,d.accept,d.present]
def scalarOut (d : Store) (i : Fin 3) (pos : ℕ) (bit : Bool) : Store :=
  match i with
  | 0=>{d with codePos:=pos,halt:=bit}
  | 1=>{d with codePos:=pos,accept:=bit}
  | 2=>{d with codePos:=pos,present:=bit}
noncomputable def scalarProgram (i : Fin 3) := RecoveryFocus.machine (scalarSlots i) LookupReadBit.machine

theorem scalar_place (i : Fin 3) (q : Fin 3) (d : Store) (pos : ℕ) (bit : Bool) :
    RecoveryFocus.config (scalarSlots i) (cfg q d).heads (cfg q d).tapes
      (LookupReadBit.cfg q (frame d.code) pos bit)=cfg q (scalarOut d i pos bit) := by
  fin_cases i
  all_goals apply TransitionEvent.focused_eq _ (by decide) (cfg q d)
  all_goals first
    | rfl
    | (intro z; fin_cases z <;> rfl)
    | (intro z h; fin_cases z <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl) | rfl)

theorem scalar_run (i : Fin 3) (d : Store) (pre tail : List Bool) (bit : Bool)
    (hs : frame d.code=pre++true::bit::tail) (hp : d.codePos=pre.length) :
    ∃ r,runFrom (scalarProgram i) 2 (cfg (scalarProgram i).start d)=some r ∧
      r.final=cfg r.final.control (scalarOut d i (d.codePos+2) bit) ∧ r.steps=2 := by
  obtain ⟨base,hb,hbf,hbs⟩ := LookupReadBit.read_run pre tail bit (scalar d i)
  rw [←hs,←hp] at hb hbf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config (scalarSlots i) (by fin_cases i <;> decide)
    LookupReadBit.machine (cfg (0 : Fin 3) d).heads (cfg (0 : Fin 3) d).tapes _ _ base hb
  have hi := scalar_place i 0 d d.codePos (scalar d i)
  have he : scalarOut d i d.codePos (scalar d i)=d := by fin_cases i <;> rfl
  rw [he] at hi
  rw [hi] at hr
  have ho : RecoveryFocus.config (scalarSlots i) (cfg (0 : Fin 3) d).heads (cfg (0 : Fin 3) d).tapes
      base.final=cfg (2 : Fin 3) (scalarOut d i (d.codePos+2) bit) := by
    rw [hbf]
    exact scalar_place i 2 d _ bit
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans hbs⟩

theorem claimed_place (q : Fin 10) (d : Store) (target : List Bool) :
    RecoveryFocus.config claimedSlots (cfg q d).heads (cfg q d).tapes
      (LookupRetainField.cappedCfg q d.scans d.scanPos target d.t d.code.length)=
      cfg q {d with scanCopy:=target} := by
  apply TransitionEvent.focused_eq claimedSlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 1 rfl) | rfl

theorem claimed_run (d : Store) (pre bits tail : List Bool)
    (hs : d.scans=pre++Streaming.marks bits++tail) (hp : d.scanPos=pre.length)
    (hl : bits.length=d.t) (hb : d.scanCopy.length≤2*d.t+1) :
    ∃ r,runFrom claimedProgram (7*d.t+5) (cfg claimedProgram.start d)=some r ∧
      r.final=cfg r.final.control (claimed d bits) ∧ r.steps=7*d.t+5 := by
  obtain ⟨base,hbase,hbf,hbs⟩ := LookupRetainField.capped_field_run pre bits tail d.scanCopy d.code.length (by omega)
  rw [←hs,←hp,hl] at hbase hbf
  rw [hl] at hbs
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config claimedSlots (by decide) LookupRetainField.machine
    (cfg LookupRetainField.machine.start d).heads (cfg LookupRetainField.machine.start d).tapes _ _ base hbase
  have hi := claimed_place LookupRetainField.machine.start d d.scanCopy
  rw [show ({d with scanCopy:=d.scanCopy} : Store)=d from rfl] at hi
  rw [hi] at hr
  have ho : RecoveryFocus.config claimedSlots (cfg LookupRetainField.machine.start d).heads
      (cfg LookupRetainField.machine.start d).tapes base.final=cfg (9 : Fin 10) (claimed d bits) := by
    rw [hbf]
    exact claimed_place 9 d (frame bits)
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans hbs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime

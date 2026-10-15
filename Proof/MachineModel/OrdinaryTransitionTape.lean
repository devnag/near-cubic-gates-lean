import Proof.MachineModel.OrdinaryTransitionEventRun
import Proof.MachineModel.OrdinaryClaimedAction

/-! The per-tape transition parent uses one shared physical layout for tag
selection, event production, serial increment and head update. Source cursors
and the global event append cursor remain present throughout local calls. -/
namespace NearCubicWires.RepairOrdinary.TransitionTape
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  source : List Bool
  pos : ℕ
  scans : List Bool
  cursor : ℕ
  head : HeadUpdate.Store
  serial : ℕ
  tape : ℕ
  out : List Bool
  read : Bool
  after : Bool

def cfg {s : ℕ} (q : Fin s) (d : Store) (w cap : ℕ) : Configuration 16 s :=
  ⟨q,fun i => if i.val=0 then d.pos else if i.val=5 then d.cursor else if i.val=14 then d.out.length else 0,
    fun i => match i.val with
      | 0 => d.source
      | 1 => [d.read]
      | 2 => [d.after]
      | 3 => [HeadUpdate.low d.head.move]
      | 4 => [HeadUpdate.high d.head.move]
      | 5 => d.scans
      | 6 => frame (binary w d.head.head)
      | 7 => frame (binary w 1)
      | 8 => d.head.difference
      | 9 => [d.head.flag]
      | 10 => List.replicate cap false
      | 11 => List.replicate cap false
      | 12 => binary (2*w) d.serial
      | 13 => List.replicate (2*w) true
      | 14 => d.out
      | 15 => frame (binary w d.tape)
      | _ => []⟩

def actionSlots : Fin 6 → Fin 16 := ![0,1,2,3,4,5]
def eventSlots : Fin 9 → Fin 16 := ![12,13,14,10,6,7,15,1,2]
def headSlots : Fin 8 → Fin 16 := ![6,7,8,9,10,11,3,4]
noncomputable def actionProgram := RecoveryFocus.machine actionSlots ClaimedAction.machine
noncomputable def eventProgram := RecoveryFocus.machine eventSlots TransitionEvent.machine
noncomputable def headProgram := RecoveryFocus.machine headSlots HeadUpdate.machine

def selected (d : Store) (bits : TagMachine.Word) (bit : Bool) : Store :=
  {d with pos:=d.pos+8,cursor:=d.cursor+2,read:=bit,after:=TransitionTag.after bits bit,head:={d.head with move:=decodeMove [bits 2,bits 3]}}

def eventStore (d : Store) (w cap : ℕ) : TransitionEvent.Store :=
  ⟨binary (2*w) d.serial,binary w d.head.head,binary w 1,binary w d.tape,
    d.out,d.read,d.after,cap⟩
def emitted (d : Store) (w cap : ℕ) : Store :=
  {d with serial:=d.serial+1,out:=d.out++TransitionEvent.record (eventStore d w cap)}
def updated (d : Store) (w : ℕ) : Store := {d with head:=HeadUpdate.finished d.head w}

theorem action_place {s : ℕ} (q : Fin s) (d : Store) (w cap pos cursor : ℕ)
    (read after : Bool) (move : HeadMove) :
    RecoveryFocus.config actionSlots (cfg q d w cap).heads (cfg q d w cap).tapes
      (ClaimedAction.cfg q d.source pos d.scans cursor read after
        (HeadUpdate.low move) (HeadUpdate.high move))=
      cfg q {d with pos:=pos,cursor:=cursor,read:=read,after:=after,head:={d.head with move:=move}} w cap := by
  apply TransitionEvent.focused_eq actionSlots (by decide) (cfg q d w cap)
  · rfl
  · intro j; fin_cases j <;> simp [ClaimedAction.cfg,TransitionTag.cfg,TapeEmbedding.config,
      Fin.addCases,cfg,actionSlots]
  · intro j; fin_cases j <;> simp [ClaimedAction.cfg,TransitionTag.cfg,TapeEmbedding.config,
      Fin.addCases,cfg,actionSlots]
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl) | exact False.elim (h 5 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 1 rfl) | exact False.elim (h 2 rfl) | exact False.elim (h 3 rfl) | exact False.elim (h 4 rfl)

theorem action_run (d : Store) (w cap : ℕ) (tagPre tagTail scanPre scanTail : List Bool)
    (bits : TagMachine.Word) (bit : Bool)
    (hv : TagMachine.valid true bits=true)
    (ht : d.source=tagPre++Streaming.marks (TagMachine.tagWord bits)++tagTail)
    (hp : d.pos=tagPre.length) (hs : d.scans=scanPre++true::bit::scanTail)
    (hc : d.cursor=scanPre.length) :
    ∃ r,runFrom actionProgram 14 (cfg actionProgram.start d w cap)=some r ∧
      r.final=cfg ((RecoveryCalls.controlCode TransitionTag.sizes none).natAdd 3)
        (selected d bits bit) w cap ∧ r.steps=14 := by
  obtain ⟨base,hb,hf,hstep⟩ := ClaimedAction.action_run tagPre tagTail scanPre scanTail bits
    bit d.read d.after (HeadUpdate.low d.head.move) (HeadUpdate.high d.head.move)
  have hb' : runFrom ClaimedAction.machine 14
      (ClaimedAction.cfg ClaimedAction.machine.start d.source d.pos d.scans d.cursor
        d.read d.after (HeadUpdate.low d.head.move) (HeadUpdate.high d.head.move))=some base := by
    simpa only [ht,hp,hs,hc] using hb
  obtain ⟨r,hr,hrf,hsteps⟩ := RecoveryFocus.run_config actionSlots (by decide) _
    (cfg actionProgram.start d w cap).heads (cfg actionProgram.start d w cap).tapes _ _ base hb'
  have hi := action_place actionProgram.start d w cap d.pos d.cursor d.read d.after d.head.move
  have hsame : ({d with pos:=d.pos,cursor:=d.cursor,read:=d.read,after:=d.after,head:={d.head with move:=d.head.move}} : Store)=d := rfl
  rw [hsame] at hi
  have hi' : RecoveryFocus.config actionSlots (cfg actionProgram.start d w cap).heads
      (cfg actionProgram.start d w cap).tapes (ClaimedAction.cfg ClaimedAction.machine.start
        d.source d.pos d.scans d.cursor d.read d.after (HeadUpdate.low d.head.move) (HeadUpdate.high d.head.move))=
      cfg actionProgram.start d w cap := hi
  rw [hi'] at hr
  refine ⟨r,hr,?_,hsteps.trans hstep⟩
  rw [hrf,hf]
  obtain ⟨hlo,hhi⟩ := TransitionTag.move_flags bits hv
  have he := action_place ((RecoveryCalls.controlCode TransitionTag.sizes none).natAdd 3)
    d w cap (d.pos+8) (d.cursor+2) bit (TransitionTag.after bits bit) (decodeMove [bits 2,bits 3])
  rw [hlo,hhi] at he
  rw [← ht,← hp,← hs,← hc]
  exact he

theorem event_place {s : ℕ} (q : Fin s) (d : Store) (w cap serial : ℕ) (out : List Bool) :
    RecoveryFocus.config eventSlots (cfg q d w cap).heads (cfg q d w cap).tapes
      (TransitionEvent.cfg q {eventStore d w cap with serial:=binary (2*w) serial,out:=out})=
      cfg q {d with serial:=serial,out:=out} w cap := by
  apply TransitionEvent.focused_eq eventSlots (by decide) (cfg q d w cap)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> simp [TransitionEvent.cfg,eventStore,eventSlots,cfg]
  · intro i h; fin_cases i <;> first | exact False.elim (h 2 rfl) | rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 2 rfl) | rfl

theorem event_run (d : Store) (w cap : ℕ) (hs : d.serial+1<2^(2*w)) (hc : 4*w+3≤cap) :
    ∃ r,runFrom eventProgram (TransitionEvent.budget (2*w) w)
      (cfg eventProgram.start d w cap)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode TransitionEvent.sizes none) (emitted d w cap) w cap := by
  obtain ⟨base,hb,hf,_⟩ := TransitionEvent.event_run (eventStore d w cap) (2*w) w d.serial
    rfl (by simp [eventStore]) (by simp [eventStore]) (by simp [eventStore]) hs
    (by dsimp [eventStore]; omega) (by dsimp [eventStore]; omega)
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config eventSlots (by decide) _
    (cfg eventProgram.start d w cap).heads (cfg eventProgram.start d w cap).tapes _ _ base hb
  have hi := event_place eventProgram.start d w cap d.serial d.out
  have hi' : RecoveryFocus.config eventSlots (cfg eventProgram.start d w cap).heads
      (cfg eventProgram.start d w cap).tapes (TransitionEvent.cfg TransitionEvent.machine.start (eventStore d w cap))=
      cfg eventProgram.start d w cap := hi
  rw [hi'] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact event_place (RecoveryCalls.controlCode TransitionEvent.sizes none) d w cap _ _

theorem head_place {s : ℕ} (q : Fin s) (d : Store) (w cap : ℕ) (head : HeadUpdate.Store) :
    RecoveryFocus.config headSlots (cfg q d w cap).heads (cfg q d w cap).tapes
      (⟨q,fun _ => 0,head.tapes w cap⟩ : Configuration 8 s)=cfg q {d with head:=head} w cap := by
  apply TransitionEvent.focused_eq headSlots (by decide) (cfg q d w cap)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 2 rfl) | exact False.elim (h 3 rfl) | exact False.elim (h 6 rfl) | exact False.elim (h 7 rfl) | rfl

theorem head_run (d : Store) (w cap : ℕ) (hh : d.head.head+1<2^w)
    (hb : d.head.difference.length≤2*w+1) (hc : 4*w+3≤cap) :
    ∃ r,runFrom headProgram (20*(w+2)) (cfg headProgram.start d w cap)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode HeadUpdate.sizes none) (updated d w) w cap := by
  obtain ⟨base,hr,ht,hhf,_⟩ := HeadUpdate.update_run d.head w cap hh hb hc
  obtain ⟨r,hrun,hfinal,_⟩ := RecoveryFocus.run_config headSlots (by decide) _
    (cfg headProgram.start d w cap).heads (cfg headProgram.start d w cap).tapes _ _ base hr
  have hi := head_place headProgram.start d w cap d.head
  have hi' : RecoveryFocus.config headSlots (cfg headProgram.start d w cap).heads
      (cfg headProgram.start d w cap).tapes (initialConfiguration HeadUpdate.machine (d.head.tapes w cap))=
      cfg headProgram.start d w cap := hi
  rw [hi'] at hrun
  have hcontrol : base.final.control=RecoveryCalls.controlCode HeadUpdate.sizes none := by
    obtain ⟨_,hh⟩ := prefix_of_run HeadUpdate.machine (20*(w+2)) _ base hr
    have hc' : (RecoveryCalls.controlCode HeadUpdate.sizes).symm base.final.control=none := by
      simpa only [HeadUpdate.machine,RecoveryCalls.machine,Option.isNone_iff_eq_none] using hh
    have he := congrArg (RecoveryCalls.controlCode HeadUpdate.sizes) hc'
    simpa only [Equiv.apply_symm_apply] using he
  have hf : base.final=(⟨RecoveryCalls.controlCode HeadUpdate.sizes none,fun _ => 0,
      (HeadUpdate.finished d.head w).tapes w cap⟩ : Configuration 8 _) := by
    apply configuration_ext
    · exact hcontrol
    · exact funext hhf
    · exact ht
  refine ⟨r,hrun,?_⟩
  rw [hfinal,hf]
  exact head_place _ d w cap _

end NearCubicWires.RepairOrdinary.TransitionTape

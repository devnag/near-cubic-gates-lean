import Proof.MachineModel.OrdinaryMemoryEmitAdvance
import Proof.MachineModel.OrdinaryKeyField
import Proof.MachineModel.OrdinaryHeadUpdate

/-! The transition consumer serializes the physical head and tape-id fields
directly. Their concatenation is the exact cell key; no computed address or
prepared raw key is supplied. The global output remains at its append cursor. -/
namespace NearCubicWires.RepairOrdinary.TransitionEvent
open LocalBitMultitape RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focused_eq {t u s : ℕ} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (ambient target : Configuration u s) (source : Configuration t s)
    (hq : source.control=target.control)
    (hh : ∀ j,source.heads j=target.heads (slot j))
    (ht : ∀ j,source.tapes j=target.tapes (slot j))
    (oh : ∀ i,(∀ j,slot j≠i) → ambient.heads i=target.heads i)
    (ot : ∀ i,(∀ j,slot j≠i) → ambient.tapes i=target.tapes i) :
    RecoveryFocus.config slot ambient.heads ambient.tapes source=target := by
  apply configuration_ext
  · exact hq
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none =>
      simp only [RecoveryFocus.config,hp]
      apply oh i
      intro j hj
      subst i
      rw [RecoveryFocus.pick_slot slot hi] at hp
      contradiction
    | some j =>
      simp only [RecoveryFocus.config,hp]
      rw [← RecoveryFocus.slot_of_pick slot hp]
      exact hh j
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none =>
      simp only [RecoveryFocus.config,hp]
      apply ot i
      intro j hj
      subst i
      rw [RecoveryFocus.pick_slot slot hi] at hp
      contradiction
    | some j =>
      simp only [RecoveryFocus.config,hp]
      rw [← RecoveryFocus.slot_of_pick slot hp]
      exact ht j

theorem cell_key (w head tape : ℕ) (hh : head<2^w) (ht : tape<2^w) :
    binary w head++binary w tape++[false,false]=binary (2*w+2) (tape*2^w+head) := by
  have h := BoundedCounter.binary_of_value (binary w head++binary w tape++[false,false])
  have hv : value (binary w head++binary w tape++[false,false])=tape*2^w+head := by
    simp [value_append,binary_value _ _ hh,binary_value _ _ ht,value,Nat.mul_comm,Nat.add_comm]
  rw [hv] at h
  simpa [Nat.two_mul,Nat.add_assoc] using h.symm

structure Store where
  serial : List Bool
  head : List Bool
  template : List Bool
  tape : List Bool
  out : List Bool
  read : Bool
  after : Bool
  cap : ℕ

def cfg {s : ℕ} (q : Fin s) (d : Store) : Configuration 9 s :=
  ⟨q,![0,0,d.out.length,0,0,0,0,0,0],
    ![d.serial,List.replicate d.serial.length true,d.out,List.replicate d.cap false,
      frame d.head,frame d.template,frame d.tape,[d.read],[d.after]]⟩

def append (d : Store) (bits : List Bool) : Store := {d with out:=d.out++bits}

def headerBits (d : Store) : Fin 4 → Bool := ![true,d.read,true,d.after]
def header : Machine 9 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bits => if h:q.val<4 then
    some ⟨⟨q.val+1,by omega⟩,fun i => if i.val=2 then
      some (![true,bits 7,true,bits 8] ⟨q.val,h⟩) else none,
      fun i => if i.val=2 then .right else .stay⟩ else none

theorem header_step (p : Fin 4) (d : Store) :
    step header (cfg p.castSucc d)=some (cfg p.succ (append d [headerBits d p])) := by
  fin_cases p <;> simp [step,header,cfg,Configuration.scanned,readTapeBit]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction,HeadMove.apply,append,headerBits,Streaming.write_append])

theorem header_run (d : Store) :
    ∃ r,runFrom header 4 (cfg 0 d)=some r ∧
      r.final=cfg 4 (append d [true,d.read,true,d.after]) := by
  have p0 := Timed.single (by rfl : header.halted (0 : Fin 5)=false) (header_step 0 d)
  have p1 := Timed.single (by rfl : header.halted (1 : Fin 5)=false)
    (header_step 1 (append d [true]))
  have p2 := Timed.single (by rfl : header.halted (2 : Fin 5)=false)
    (header_step 2 (append d [true,d.read]))
  have p3 := Timed.single (by rfl : header.halted (3 : Fin 5)=false)
    (header_step 3 (append d [true,d.read,true]))
  simp [append,headerBits,List.append_assoc] at p0 p1 p2 p3
  have h : Timed header 4 (cfg 0 d) (cfg 4 (append d [true,d.read,true,d.after])) := by
    simpa [append,headerBits,List.append_assoc] using ((p0.trans p1).trans p2).trans p3
  obtain ⟨r,hr,hf,_⟩ := h.run (by rfl)
  exact ⟨r,hr,hf⟩

def tailBits : Fin 5 → Bool := ![true,false,true,false,false]
def close : Machine 9 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==5
  rule := fun q _ => if h:q.val<5 then
    some ⟨⟨q.val+1,by omega⟩,fun i => if i.val=2 then some (tailBits ⟨q.val,h⟩) else none,
      fun i => if i.val=2 then .right else .stay⟩ else none

theorem close_step (p : Fin 5) (d : Store) :
    step close (cfg p.castSucc d)=some (cfg p.succ (append d [tailBits p])) := by
  fin_cases p <;> simp [step,close,cfg]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction,HeadMove.apply,append,tailBits,Streaming.write_append])

theorem close_run (d : Store) :
    ∃ r,runFrom close 5 (cfg 0 d)=some r ∧
      r.final=cfg 5 (append d [true,false,true,false,false]) := by
  have p0 := Timed.single (by rfl : close.halted (0 : Fin 6)=false) (close_step 0 d)
  have p1 := Timed.single (by rfl : close.halted (1 : Fin 6)=false) (close_step 1 (append d [true]))
  have p2 := Timed.single (by rfl : close.halted (2 : Fin 6)=false) (close_step 2 (append d [true,false]))
  have p3 := Timed.single (by rfl : close.halted (3 : Fin 6)=false) (close_step 3 (append d [true,false,true]))
  have p4 := Timed.single (by rfl : close.halted (4 : Fin 6)=false) (close_step 4 (append d [true,false,true,false]))
  simp [append,tailBits,List.append_assoc] at p0 p1 p2 p3 p4
  have h : Timed close 5 (cfg 0 d) (cfg 5 (append d [true,false,true,false,false])) := by
    simpa [append,tailBits,List.append_assoc] using (((p0.trans p1).trans p2).trans p3).trans p4
  obtain ⟨r,hr,hf,_⟩ := h.run (by rfl)
  exact ⟨r,hr,hf⟩

def serialSlots : Fin 4 → Fin 9 := ![0,1,2,3]
def headSlots : Fin 4 → Fin 9 := ![4,5,2,3]
def tapeSlots : Fin 4 → Fin 9 := ![6,5,2,3]
def counterSlots : Fin 2 → Fin 9 := ![0,3]
noncomputable def serialProgram := RecoveryFocus.machine serialSlots (MemoryEmitReady.machine false)
noncomputable def headProgram := RecoveryFocus.machine headSlots KeyPrefix.machine
noncomputable def tapeProgram := RecoveryFocus.machine tapeSlots KeyPrefix.machine
noncomputable def counterProgram := RecoveryFocus.machine counterSlots (Rewind.machine BinaryIncrement.machine)

theorem serial_place {s : ℕ} (q : Fin s) (d : Store) (out : List Bool) :
    RecoveryFocus.config serialSlots (cfg q d).heads (cfg q d).tapes
      (MemoryEmitReady.config q d.serial out d.cap) = cfg q {d with out:=out} := by
  apply focused_eq serialSlots (by decide) (cfg q d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)

theorem head_place {s : ℕ} (q : Fin s) (d : Store) (out : List Bool) :
    RecoveryFocus.config headSlots (cfg q d).heads (cfg q d).tapes
      (KeyPrefix.ready q (frame d.head) (frame d.template) out d.cap) = cfg q {d with out:=out} := by
  apply focused_eq headSlots (by decide) (cfg q d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)

theorem tape_place {s : ℕ} (q : Fin s) (d : Store) (out : List Bool) :
    RecoveryFocus.config tapeSlots (cfg q d).heads (cfg q d).tapes
      (KeyPrefix.ready q (frame d.tape) (frame d.template) out d.cap) = cfg q {d with out:=out} := by
  apply focused_eq tapeSlots (by decide) (cfg q d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)

theorem serial_run (d : Store) (hc : 2*d.serial.length+1≤d.cap) :
    ∃ r,runFrom serialProgram (4*d.serial.length+4) (cfg 0 d)=some r ∧
      r.final=cfg 4 (append d (Streaming.marks d.serial)) := by
  obtain ⟨base,hb,hf,_⟩ := MemoryEmitReady.field_run false d.serial d.out d.cap hc
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config serialSlots (by decide) _
    (cfg (0 : Fin 5) d).heads (cfg (0 : Fin 5) d).tapes _ _ base hb
  rw [serial_place] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  have he : MemoryEmitField.suffix false=[] := rfl
  rw [he,List.append_nil]
  exact serial_place (4 : Fin 5) d (d.out++Streaming.marks d.serial)

theorem head_run (d : Store) (hw : d.head.length=d.template.length) (hc : 2*d.head.length≤d.cap) :
    ∃ r,runFrom headProgram (4*d.head.length+2) (cfg 0 d)=some r ∧
      r.final=cfg 3 (append d (Streaming.marks d.head)) := by
  obtain ⟨base,hb,hf,_,_⟩ := KeyPrefix.field_run d.head [false] d.template d.out d.cap hw hc
  have he : Streaming.marks d.head++[false]=frame d.head := by
    simpa only [List.append_nil,frame] using (Streaming.frame_append d.head []).symm
  rw [he] at hb hf
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config headSlots (by decide) _
    (cfg (0 : Fin 4) d).heads (cfg (0 : Fin 4) d).tapes _ _ base hb
  rw [head_place] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact head_place (3 : Fin 4) d _

theorem tape_run (d : Store) (hw : d.tape.length=d.template.length) (hc : 2*d.tape.length≤d.cap) :
    ∃ r,runFrom tapeProgram (4*d.tape.length+2) (cfg 0 d)=some r ∧
      r.final=cfg 3 (append d (Streaming.marks d.tape)) := by
  obtain ⟨base,hb,hf,_,_⟩ := KeyPrefix.field_run d.tape [false] d.template d.out d.cap hw hc
  have he : Streaming.marks d.tape++[false]=frame d.tape := by
    simpa only [List.append_nil,frame] using (Streaming.frame_append d.tape []).symm
  rw [he] at hb hf
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config tapeSlots (by decide) _
    (cfg (0 : Fin 4) d).heads (cfg (0 : Fin 4) d).tapes _ _ base hb
  rw [tape_place] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact tape_place (3 : Fin 4) d _

end NearCubicWires.RepairOrdinary.TransitionEvent

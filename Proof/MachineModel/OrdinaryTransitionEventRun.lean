import Proof.MachineModel.OrdinaryTransitionEvent
import Proof.Foundations.OrdinaryRewindCarrier

/-! A whole physical transition event, including paid serial increment. The
two short coordinate fields are consumed by the same stream serializer. -/
namespace NearCubicWires.RepairOrdinary.TransitionEvent
open LocalBitMultitape RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_place (q : Fin 4) (d : Store) (bits : List Bool)
    (hl : bits.length=d.serial.length) :
    RecoveryFocus.config counterSlots (cfg q d).heads (cfg q d).tapes
      (RankScalar.scalarConfig q bits 0 (List.replicate d.cap false) 0) =
      cfg q {d with serial:=bits} := by
  apply focused_eq counterSlots (by decide) (cfg q d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl) | simp [cfg,hl]

theorem counter_run (d : Store) (I serial : ℕ) (he : d.serial=binary I serial)
    (hs : serial+1<2^I) (hc : I≤d.cap) :
    ∃ r,runFrom counterProgram (2*I+2) (cfg 0 d)=some r ∧
      r.final=cfg 3 {d with serial:=binary I (serial+1)} := by
  obtain ⟨base,hb,hf⟩ := MemoryEmitCounter.increment_run I serial d.cap hs hc
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config counterSlots (by decide) _
    (cfg (0 : Fin 4) d).heads (cfg (0 : Fin 4) d).tapes _ _ base hb
  have hi := counter_place 0 d (binary I serial) (by simp [he])
  have hid : ({d with serial:=binary I serial} : Store)=d := by rw [← he]
  rw [hid] at hi
  rw [hi] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact counter_place 3 d _ (by simp [he])

def sizes : Fin 6 → ℕ := ![5,5,4,4,6,4]
instance (j : Fin 6) : NeZero (sizes j) := ⟨by fin_cases j <;> decide⟩
noncomputable def programs : (j : Fin 6) → Machine 9 (sizes j)
  | ⟨0,_⟩ => header
  | ⟨1,_⟩ => serialProgram
  | ⟨2,_⟩ => headProgram
  | ⟨3,_⟩ => tapeProgram
  | ⟨4,_⟩ => close
  | ⟨5,_⟩ => counterProgram
  | ⟨n+6,h⟩ => False.elim (by omega)
def next (j : Fin 6) (_ : Fin (sizes j)) (_ : Fin 9 → Bool) : Option (Fin 6) :=
  if h:j.val<5 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 6) (d e : Store) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 9 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : ∀ c bits,next j c bits=some k) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh (hn _ _)
  have h := hb.trans (Timed.single
    (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

theorem stop_phase (j : Fin 6) (d e : Store) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 9 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : ∀ c bits,next j c bits=none) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh (hn _ _)
  have h := hb.trans (Timed.single
    (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

def record (d : Store) : List Bool :=
  frame (d.read::d.after::d.serial++d.head++d.tape++[false,false])
def finished (d : Store) (I serial : ℕ) : Store :=
  {d with serial:=binary I (serial+1),out:=d.out++record d}
def budget (I w : ℕ) : ℕ := 6*I+8*w+25

theorem event_run (d : Store) (I w serial : ℕ)
    (hserial : d.serial=binary I serial) (hhead : d.head.length=w)
    (htape : d.tape.length=w) (htemplate : d.template.length=w)
    (hs : serial+1<2^I) (hc : 2*I+1≤d.cap) (hwc : 2*w≤d.cap) :
    ∃ r,runFrom machine (budget I w) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished d I serial) ∧
      r.steps≤budget I w := by
  let d1 := append d [true,d.read,true,d.after]
  let d2 := append d1 (Streaming.marks d.serial)
  let d3 := append d2 (Streaming.marks d.head)
  let d4 := append d3 (Streaming.marks d.tape)
  let d5 := append d4 [true,false,true,false,false]
  let d6 : Store := {d5 with serial:=binary I (serial+1)}
  obtain ⟨r0,hr0,hf0⟩ := header_run d
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d d1 4 4 r0 hr0 hf0 (by intro c bits; rfl)
  obtain ⟨r1,hr1,hf1⟩ := serial_run d1 (by simpa [d1,append,hserial] using hc)
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 2 d1 d2 4 _ r1 hr1 hf1 (by intro c bits; rfl)
  obtain ⟨r2,hr2,hf2⟩ := head_run d2 (by simp [d2,d1,append,hhead,htemplate])
    (by simpa [d2,d1,append,hhead] using hwc)
  obtain ⟨n2,hn2,hp2⟩ := call_phase 2 3 d2 d3 3 _ r2 hr2 hf2 (by intro c bits; rfl)
  obtain ⟨r3,hr3,hf3⟩ := tape_run d3 (by simp [d3,d2,d1,append,htape,htemplate])
    (by simpa [d3,d2,d1,append,htape] using hwc)
  obtain ⟨n3,hn3,hp3⟩ := call_phase 3 4 d3 d4 3 _ r3 hr3 hf3 (by intro c bits; rfl)
  obtain ⟨r4,hr4,hf4⟩ := close_run d4
  obtain ⟨n4,hn4,hp4⟩ := call_phase 4 5 d4 d5 5 5 r4 hr4 hf4 (by intro c bits; rfl)
  obtain ⟨r5,hr5,hf5⟩ := counter_run d5 I serial hserial hs (by dsimp [d5,d4,d3,d2,d1,append]; omega)
  obtain ⟨n5,hn5,hp5⟩ := stop_phase 5 d5 d6 3 _ r5 hr5 hf5 (by intro c bits; rfl)
  have hj := ((((hp0.trans hp1).trans hp2).trans hp3).trans hp4).trans hp5
  have hout : d6=finished d I serial := by
    dsimp [d6,d5,d4,d3,d2,d1,finished,append,record]
    congr 1
    simp [frame,Streaming.frame_append,List.append_assoc]
  rw [hout] at hj
  have hn : n0+n1+n2+n3+n4+n5≤budget I w := by
    simp only [d3,d2,d1,append,hserial,binary_length,hhead,htape] at hn1 hn2 hn3
    dsimp [budget]
    omega
  obtain ⟨r,hr,hf,hsr⟩ := hj.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg])
  have hm := runFrom_moreFuel machine _ (budget I w-(n0+n1+n2+n3+n4+n5)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hf,by omega⟩

theorem record_exact (I w serial head tape cap : ℕ) (out : List Bool) (read after : Bool)
    (hh : head<2^w) (ht : tape<2^w) :
    record ⟨binary I serial,binary w head,binary w 1,binary w tape,out,read,after,cap⟩=
      frame (read::after::binary I serial++binary (2*w+2) (tape*2^w+head)) := by
  dsimp [record]
  rw [← cell_key w head tape hh ht]
  simp only [List.append_assoc]

end NearCubicWires.RepairOrdinary.TransitionEvent

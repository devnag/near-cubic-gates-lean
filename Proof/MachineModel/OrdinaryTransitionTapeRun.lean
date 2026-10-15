import Proof.MachineModel.OrdinaryTransitionTape

/-! One actual selected action becomes a chronological event, a consecutive
serial and the updated head, in one finite machine with every return charged. -/
namespace NearCubicWires.RepairOrdinary.TransitionTape
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 3 → ℕ :=
  ![3+Fintype.card (RecoveryCalls.Control TransitionTag.sizes),
    Fintype.card (RecoveryCalls.Control TransitionEvent.sizes),
    Fintype.card (RecoveryCalls.Control HeadUpdate.sizes)]
noncomputable def programs : (j : Fin 3) → Machine 16 (sizes j)
  | ⟨0,_⟩ => actionProgram
  | ⟨1,_⟩ => eventProgram
  | ⟨2,_⟩ => headProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (_ : Fin 16 → Bool) : Option (Fin 3) :=
  if j.val=0 then some 1 else if j.val=1 then some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 3) (d e : Store) (w cap : ℕ) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 16 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d w cap)=some r)
    (hf : r.final=cfg q e w cap) (hn : ∀ c bits,next j c bits=some k) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d w cap)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e w cap) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh (hn _ _)
  have h := hb.trans (Timed.single
    (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

theorem stop_phase (j : Fin 3) (d e : Store) (w cap : ℕ) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 16 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d w cap)=some r)
    (hf : r.final=cfg q e w cap) (hn : ∀ c bits,next j c bits=none) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d w cap)
      (cfg (RecoveryCalls.controlCode sizes none) e w cap) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh (hn _ _)
  have h := hb.trans (Timed.single
    (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

def finished (d : Store) (w cap : ℕ) (bits : TagMachine.Word) (bit : Bool) : Store :=
  updated (emitted (selected d bits bit) w cap) w
def budget (w : ℕ) : ℕ := 40*w+82

theorem tape_run (d : Store) (w cap : ℕ) (tagPre tagTail scanPre scanTail : List Bool)
    (bits : TagMachine.Word) (bit : Bool)
    (hv : TagMachine.valid true bits=true)
    (ht : d.source=tagPre++Streaming.marks (TagMachine.tagWord bits)++tagTail)
    (hp : d.pos=tagPre.length) (hs : d.scans=scanPre++true::bit::scanTail)
    (hc : d.cursor=scanPre.length)
    (hserial : d.serial+1<2^(2*w)) (hhead : d.head.head+1<2^w)
    (hback : d.head.difference.length≤2*w+1) (hcap : 4*w+3≤cap) :
    ∃ r,runFrom machine (budget w) (cfg machine.start d w cap)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished d w cap bits bit) w cap ∧
      r.steps≤budget w := by
  let d1 := selected d bits bit
  let d2 := emitted d1 w cap
  let d3 := updated d2 w
  obtain ⟨r0,hr0,hf0,_⟩ := action_run d w cap tagPre tagTail scanPre scanTail bits bit hv ht hp hs hc
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d d1 w cap _ 14 r0 hr0 hf0 (by intro c bits; rfl)
  obtain ⟨r1,hr1,hf1⟩ := event_run d1 w cap hserial hcap
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 2 d1 d2 w cap _ _ r1 hr1 hf1 (by intro c bits; rfl)
  obtain ⟨r2,hr2,hf2⟩ := head_run d2 w cap hhead hback hcap
  obtain ⟨n2,hn2,hp2⟩ := stop_phase 2 d2 d3 w cap _ _ r2 hr2 hf2 (by intro c bits; rfl)
  have hj := (hp0.trans hp1).trans hp2
  have hn : n0+n1+n2≤budget w := by dsimp [budget,TransitionEvent.budget] at *; omega
  obtain ⟨r,hr,hf,hsteps⟩ := hj.run
    (by simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg])
  have hm := runFrom_moreFuel machine _ (budget w-(n0+n1+n2)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hf,by omega⟩

theorem finished_head (d : Store) (w cap : ℕ) (bits : TagMachine.Word) (bit : Bool) :
    (finished d w cap bits bit).head.head=HeadMove.apply (decodeMove [bits 2,bits 3]) d.head.head := by
  exact HeadUpdate.finished_head _ _

theorem finished_difference (d : Store) (w cap : ℕ) (bits : TagMachine.Word) (bit : Bool)
    (hb : d.head.difference.length≤2*w+1) :
    (finished d w cap bits bit).head.difference.length≤2*w+1 :=
  HeadUpdate.finished_difference_bound _ _ hb

theorem finished_stream (d : Store) (w cap : ℕ) (bits : TagMachine.Word) (bit : Bool)
    (hh : d.head.head<2^w) (ht : d.tape<2^w) :
    (finished d w cap bits bit).out=d.out++frame
      (bit::TransitionTag.after bits bit::binary (2*w) d.serial++binary (2*w+2) (d.tape*2^w+d.head.head)) := by
  dsimp [finished,updated,emitted,selected,eventStore]
  rw [TransitionEvent.record_exact (2*w) w d.serial d.head.head d.tape cap d.out bit
    (TransitionTag.after bits bit) hh ht]
  rfl

theorem finished_cursors (d : Store) (w cap : ℕ) (bits : TagMachine.Word) (bit : Bool) :
    (finished d w cap bits bit).source=d.source ∧ (finished d w cap bits bit).pos=d.pos+8 ∧
    (finished d w cap bits bit).scans=d.scans ∧ (finished d w cap bits bit).cursor=d.cursor+2 ∧
    (finished d w cap bits bit).serial=d.serial+1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.TransitionTape

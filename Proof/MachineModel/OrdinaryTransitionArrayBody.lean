import Proof.MachineModel.OrdinaryTransitionArrayTapes

/-! One array iteration loads a physical head field, executes the selected
tape action, appends its new head, and advances the physical tape-id field. -/
namespace NearCubicWires.RepairOrdinary.TransitionArray
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 4 → ℕ := ![4,Fintype.card (RecoveryCalls.Control TransitionTape.sizes),6,5]
noncomputable def programs : (j : Fin 4) → Machine 18 (sizes j)
  | ⟨0,_⟩ => loadProgram
  | ⟨1,_⟩ => tapeProgram
  | ⟨2,_⟩ => appendProgram
  | ⟨3,_⟩ => incrementProgram
  | ⟨n+4,h⟩ => False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 18 → Bool) : Option (Fin 4) :=
  if h:j.val<3 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 4) (d e : TransitionTape.Store) (w cap : ℕ) (source : List Bool)
    (pos nextPos : ℕ) (out nextOut : List Bool) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 18 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d w cap source pos out)=some r)
    (hf : r.final=cfg q e w cap source nextPos nextOut) (hn : ∀ c bits,next j c bits=some k) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d w cap source pos out)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e w cap source nextPos nextOut) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh (hn _ _)
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

theorem stop_phase (j : Fin 4) (d e : TransitionTape.Store) (w cap : ℕ) (source : List Bool)
    (pos nextPos : ℕ) (out nextOut : List Bool) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 18 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d w cap source pos out)=some r)
    (hf : r.final=cfg q e w cap source nextPos nextOut) (hn : ∀ c bits,next j c bits=none) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d w cap source pos out)
      (cfg (RecoveryCalls.controlCode sizes none) e w cap source nextPos nextOut) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh (hn _ _)
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

def executed (d : TransitionTape.Store) (w cap head : ℕ) (bits : TagMachine.Word) (bit : Bool) : TransitionTape.Store :=
  TransitionTape.finished (loaded d head) w cap bits bit
def finished (d : TransitionTape.Store) (w cap head : ℕ) (bits : TagMachine.Word) (bit : Bool) : TransitionTape.Store :=
  {executed d w cap head bits bit with tape:=d.tape+1}
def bodyBudget (w : ℕ) : ℕ := 52*w+95

theorem body_run (d : TransitionTape.Store) (w cap head : ℕ) (pre post out : List Bool)
    (tagPre tagTail scanPre scanTail : List Bool) (bits : TagMachine.Word) (bit : Bool)
    (hv : TagMachine.valid true bits=true)
    (ht : d.source=tagPre++Streaming.marks (TagMachine.tagWord bits)++tagTail)
    (hp : d.pos=tagPre.length) (hs : d.scans=scanPre++true::bit::scanTail)
    (hc : d.cursor=scanPre.length) (hserial : d.serial+1<2^(2*w))
    (hhead : head+1<2^w) (htape : d.tape+1<2^w)
    (hback : d.head.difference.length≤2*w+1) (hcap : 4*w+3≤cap) :
    ∃ r,runFrom machine (bodyBudget w)
      (cfg machine.start d w cap (pre++frame (binary w head)++post) pre.length out)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished d w cap head bits bit) w cap
        (pre++frame (binary w head)++post) (pre.length+2*w+1)
        (out++frame (binary w (executed d w cap head bits bit).head.head)) ∧
      r.steps≤bodyBudget w := by
  let source := pre++frame (binary w head)++post
  let pos := pre.length+2*w+1
  let d0 := loaded d head
  let d1 := executed d w cap head bits bit
  let out1 := out++frame (binary w d1.head.head)
  let d2 := finished d w cap head bits bit
  obtain ⟨r0,hr0,hf0⟩ := load_run d w cap head pre post out (by omega)
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d d0 w cap source pre.length pos out out _ _ r0 hr0 hf0
    (by intro c bits; rfl)
  obtain ⟨r1,hr1,hf1⟩ := tape_run d0 w cap source pos out tagPre tagTail scanPre scanTail bits bit
    hv ht hp hs hc hserial hhead hback hcap
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 2 d0 d1 w cap source pos pos out out _ _ r1 hr1 hf1
    (by intro c bits; rfl)
  obtain ⟨r2,hr2,hf2⟩ := append_run d1 w cap source pos out (by omega)
  obtain ⟨n2,hn2,hp2⟩ := call_phase 2 3 d1 d1 w cap source pos pos out out1 _ _ r2 hr2 hf2
    (by intro c bits; rfl)
  obtain ⟨r3,hr3,hf3⟩ := increment_run d1 w cap source pos out1 htape (by omega)
  obtain ⟨n3,hn3,hp3⟩ := stop_phase 3 d1 d2 w cap source pos pos out1 out1 _ _ r3 hr3 hf3
    (by intro c bits; rfl)
  have hj := ((hp0.trans hp1).trans hp2).trans hp3
  have hn : n0+n1+n2+n3≤bodyBudget w := by
    dsimp [TransitionTape.budget] at hn1
    dsimp [bodyBudget]
    omega
  obtain ⟨r,hr,hf,hsteps⟩ := hj.run
    (by simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg,TapeEmbedding.config,TransitionTape.cfg])
  have hm := runFrom_moreFuel machine _ (bodyBudget w-(n0+n1+n2+n3)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hf,by omega⟩

end NearCubicWires.RepairOrdinary.TransitionArray

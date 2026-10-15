import Proof.MachineModel.OrdinaryTransitionWalkGuard

/-! The actual rule/halt branch of the transition loop. Its fields and
branch outcome are read from the paid literal lookup on the same verifier. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure LookupReady (d : Store) : Prop where
  tags_zero : d.tagPos=0
  position : d.lookup.codePos≤2*d.lookup.code.length+1
  capacity : 2*(d.lookup.t+d.lookup.j)+2≤d.lookup.cap
  scanCopy : d.lookup.scanCopy.length≤2*d.lookup.t+1
  flagQuery : d.lookup.flagQuery.length≤2*d.lookup.j+1
  flagCounter : d.lookup.flagCounter.length≤2*d.lookup.j+1
  query : d.lookup.query.length≤2*(d.lookup.t+d.lookup.j)+1
  counter : d.lookup.counter.length≤2*(d.lookup.t+d.lookup.j)+1
  nextState : d.lookup.nextState.length≤2*d.lookup.j+1
  tags : d.lookup.tags.length≤8*d.lookup.t+1

def selected (d : Store) (bits : List Bool) : Store :=
  {d with lookup:=LookupRuntime.finished d.lookup bits,tagPos:=0}

def selectedNode (halt present : Bool) : Fin 12 := if halt || !present then 11 else 7

theorem selected_prefix (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (reads : Fin v.tapeCount→Bool) (hc : LookupRuntime.Canonical d.lookup v q) (hr : LookupReady d)
    (pre tail : List Bool) (hs : d.lookup.scans=pre++Streaming.marks (List.ofFn reads)++tail)
    (hp : d.lookup.scanPos=pre.length) :
    let node := selectedNode (v.machine.halted q) (v.machine.rule q reads).isSome
    ∃ time≤128*(d.lookup.code.length+1)^2+1,Timed machine time
      (cfg (RecoveryCalls.code sizes 6 (programs 6).start) d)
      (cfg (RecoveryCalls.code sizes node (programs node).start) (selected d (List.ofFn reads))) := by
  dsimp only
  obtain ⟨base,hbase,hbf,_,_,_,_,_,_⟩ := LookupRuntime.canonical_lookup_run d.lookup v q reads hc pre tail
    hr.position hs hp hr.capacity hr.scanCopy hr.flagQuery hr.flagCounter hr.query hr.counter hr.nextState hr.tags
  obtain ⟨r,hrun,hf,_⟩ := lift_exact LookupRuntime.machine d (LookupRuntime.finished d.lookup (List.ofFn reads))
    (RecoveryCalls.controlCode LookupRuntime.sizes none) _ base hr.tags_zero hbase hbf
  have hf' : r.final=cfg r.final.control (selected d (List.ofFn reads)) := by rw [hf]; rfl
  have hout := hc.finished_fields reads
  have hhalt : (selected d (List.ofFn reads)).lookup.halt=v.machine.halted q := hout.1
  have hpresent : (selected d (List.ofFn reads)).lookup.present=(v.machine.rule q reads).isSome := by
    change (LookupRuntime.finished d.lookup (List.ofFn reads)).present=(v.machine.rule q reads).isSome
    have h := hout.2.2.1
    cases ha:v.machine.rule q reads <;> simpa only [ha,actionCode,List.getD,List.getElem?_cons_zero,Option.getD_some,Option.isSome] using h
  apply call_phase 6 (selectedNode (v.machine.halted q) (v.machine.rule q reads).isSome)
    d (selected d (List.ofFn reads)) _ r hrun hf'
  rw [hf']
  change (if (selected d (List.ofFn reads)).lookup.halt || !(selected d (List.ofFn reads)).lookup.present
    then some 11 else some 7)=some (selectedNode (v.machine.halted q) (v.machine.rule q reads).isSome)
  rw [hhalt,hpresent]
  unfold selectedNode
  split <;> rfl

theorem guarded_lookup_ready (d : Store) (bits : List Bool) (hr : LookupReady d)
    (hl : bits.length=d.lookup.t) : LookupReady (guarded d bits) := by
  refine ⟨rfl,hr.position,hr.capacity,?_,hr.flagQuery,hr.flagCounter,hr.query,hr.counter,hr.nextState,hr.tags⟩
  change (frame bits).length≤2*d.lookup.t+1
  simp only [frame_length,hl]
  exact Nat.le_refl _

theorem guarded_canonical (d : Store) (bits : List Bool) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (hc : LookupRuntime.Canonical d.lookup v q) : LookupRuntime.Canonical (guarded d bits).lookup v q :=
  ⟨hc.code_eq,hc.tapes_eq,hc.states_eq,hc.width_eq,hc.state_eq⟩

end NearCubicWires.RepairOrdinary.TransitionWalk

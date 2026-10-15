import Proof.MachineModel.OrdinaryTransitionWalkArray

/-! Reusable endpoints of one emitted transition, and the bounded state
invariant carried by the binary-counted execution loop. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem roundDone_lookup (d : Store) (entries : List TransitionArray.Item) (nextBits : List Bool) :
    (roundDone d entries nextBits).lookup=
      {d.lookup with state:=nextBits,scanPos:=d.lookup.scanPos+2*entries.length} := by
  obtain ⟨hs,_,hsc,hcursor,_,_⟩ := walk_cursors d.w d.cap (eventStore d) entries
  change (TransitionArray.walk d.w d.cap (eventStore d) entries).source=d.lookup.tags at hs
  change (TransitionArray.walk d.w d.cap (eventStore d) entries).scans=d.lookup.scans at hsc
  change (TransitionArray.walk d.w d.cap (eventStore d) entries).cursor=d.lookup.scanPos+2*entries.length at hcursor
  change ({d.lookup with
    tags:=(TransitionArray.walk d.w d.cap (eventStore d) entries).source,
    scans:=(TransitionArray.walk d.w d.cap (eventStore d) entries).scans,
    scanPos:=(TransitionArray.walk d.w d.cap (eventStore d) entries).cursor,
    state:=nextBits} : LookupRuntime.Store)=_
  rw [hs,hsc,hcursor]

theorem roundDone_counters (d : Store) (entries : List TransitionArray.Item) (bits : List Bool) :
    (roundDone d entries bits).tagPos=0 ∧ (roundDone d entries bits).index=d.index+1 ∧
    (roundDone d entries bits).serial=d.serial+entries.length ∧ (roundDone d entries bits).tape=0 := by
  exact ⟨rfl,rfl,(arrayDone_cursors d entries).2.2.2.1,rfl⟩

theorem roundDone_difference (d : Store) (entries : List TransitionArray.Item) (bits : List Bool)
    (hh : d.head.difference.length≤2*d.w+1) :
    (roundDone d entries bits).head.difference.length≤2*d.w+1 :=
  walk_difference d.w d.cap (eventStore d) entries hh

theorem roundDone_stream (d : Store) (entries : List TransitionArray.Item) (bits : List Bool)
    (hh : ∀ e∈entries,e.head<2^d.w) (ht : d.tape+entries.length<2^d.w) :
    (roundDone d entries bits).out=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial
      (itemEvents d.tape entries) := walk_stream d.w d.cap (eventStore d) entries hh ht

theorem selected_lookup_ready (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (reads : Fin v.tapeCount→Bool) (hc : LookupRuntime.Canonical d.lookup v q)
    (hcap : 2*(d.lookup.t+d.lookup.j)+2≤d.lookup.cap) : LookupReady (selected d (List.ofFn reads)) := by
  have hl : (List.ofFn reads).length=d.lookup.t := by rw [List.length_ofFn,hc.tapes_eq]
  obtain ⟨hfq,hfc,hq,hcoun,hsc,hn,ht⟩ := LookupRuntime.finished_widths d.lookup (List.ofFn reads)
    hl hc.state_length (hc.table_fit reads)
  refine ⟨rfl,?_,hcap,hsc.le,hfq.le,hfc.le,hq.le,hcoun.le,hn.le,ht.le⟩
  change (LookupRuntime.finished d.lookup (List.ofFn reads)).codePos≤2*d.lookup.code.length+1
  rw [LookupRuntime.finished_position]
  have h := hc.table_fit reads
  omega

theorem roundDone_lookup_ready (d : Store) (entries : List TransitionArray.Item) (nextBits : List Bool)
    (hr : LookupReady d) : LookupReady (roundDone d entries nextBits) := by
  have hl := roundDone_lookup d entries nextBits
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [hl]
  · exact hr.position
  · exact hr.capacity
  · exact hr.scanCopy
  · exact hr.flagQuery
  · exact hr.flagCounter
  · exact hr.query
  · exact hr.counter
  · exact hr.nextState
  · exact hr.tags

structure Ready (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount) : Prop where
  lookup : LookupReady d
  canonical : LookupRuntime.Canonical d.lookup v view.control
  m_fit : d.m<2^d.w
  index_le : d.index≤d.m
  tape_zero : d.tape=0
  tape_fit : v.tapeCount<2^d.w
  serial_fit : d.serial+(d.m-d.index)*v.tapeCount<2^(2*d.w)
  heads_fit : ∀ i,view.heads i+(d.m-d.index)+1<2^d.w
  difference : d.head.difference.length≤2*d.w+1
  capacity : 4*d.w+3≤d.cap
  array_budget : TransitionArray.loopBudget d.w v.tapeCount≤d.C
  array_eq : d.array=ZeroPadding.pad d.C ((List.ofFn fun i=>frame (binary d.w (view.heads i))).flatten)
  array_blank : d.arrayOut=List.replicate d.C false

end NearCubicWires.RepairOrdinary.TransitionWalk

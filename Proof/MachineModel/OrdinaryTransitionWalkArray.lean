import Proof.MachineModel.OrdinaryTransitionWalkSelection

/-! Actual array emission, tag rewind, next-state promotion, and counted
loop return. The head arrays are reused and the event cursor never rewinds. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def arrayDone (d : Store) (entries : List TransitionArray.Item) : Store :=
  withArray d (TransitionArrayReuse.finished d.w d.cap (eventStore d) entries)
    (ZeroPadding.pad d.C (TransitionArray.nextFields d.w entries)) (List.replicate d.C false)
def tagsDone (d : Store) : Store := {d with tagPos:=0}
def stateDone (d : Store) (bits : List Bool) : Store :=
  {d with lookup:={d.lookup with state:=bits},tagPos:=0}
def roundDone (d : Store) (entries : List TransitionArray.Item) (nextBits : List Bool) : Store :=
  let after := stateDone (tagsDone (arrayDone d entries)) nextBits
  {after with index:=after.index+1}

theorem arrayDone_cursors (d : Store) (entries : List TransitionArray.Item) :
    (arrayDone d entries).tagPos=d.tagPos+8*entries.length ∧
    (arrayDone d entries).lookup.scanPos=d.lookup.scanPos+2*entries.length ∧
    (arrayDone d entries).lookup.scans=d.lookup.scans ∧
    (arrayDone d entries).serial=d.serial+entries.length ∧
    (arrayDone d entries).tape=0 := by
  obtain ⟨_,hp,hs,hc,hser,_⟩ := walk_cursors d.w d.cap (eventStore d) entries
  exact ⟨hp,hc,hs,hser,rfl⟩

theorem array_suffix (d : Store) (entries : List TransitionArray.Item) (nextBits pre tail : List Bool)
    (hlen : entries.length=d.lookup.t) (htagzero : d.tagPos=0)
    (hvalid : ∀ e∈entries,TagMachine.valid true e.tag=true)
    (hheads : ∀ e∈entries,e.head+1<2^d.w)
    (hserial : d.serial+entries.length<2^(2*d.w)) (htape : d.tape+entries.length<2^d.w)
    (hback : d.head.difference.length≤2*d.w+1) (hcap : 4*d.w+3≤d.cap)
    (hC : TransitionArray.loopBudget d.w entries.length≤d.C)
    (ha : d.array=ZeroPadding.pad d.C (TransitionArray.fields d.w entries))
    (ho : d.arrayOut=List.replicate d.C false)
    (htag : d.lookup.tags=frame (TransitionArray.tags entries))
    (hscan : d.lookup.scans=pre++Streaming.marks (TransitionArray.scans entries)++tail)
    (hcursor : d.lookup.scanPos=pre.length)
    (hnext : d.lookup.nextState=frame nextBits) (hwidth : nextBits.length=d.lookup.j)
    (hstate : d.lookup.state.length≤d.lookup.j) (hindex : d.index+1<2^d.w) :
    ∃ time≤TransitionArrayReuse.budget d.w d.C+12*d.lookup.t+7*d.lookup.j+4*d.w+13,
      Timed machine time (cfg (RecoveryCalls.code sizes 7 (programs 7).start) d)
        (cfg machine.start (roundDone d entries nextBits)) := by
  have htags : d.lookup.tags=[]++Streaming.marks (TransitionArray.tags entries)++[false] := by
    rw [htag]
    simpa only [List.nil_append,RepairOrdinary.frame,List.append_nil] using
      Streaming.frame_append (TransitionArray.tags entries) []
  obtain ⟨r0,hr0,hf0,_⟩ := array_run d entries [] [false] pre tail hvalid hheads hserial htape hback hcap hC
    ha ho htags htagzero hscan hcursor
  obtain ⟨n0,hn0,hp0⟩ := call_phase 7 8 d (arrayDone d entries) _ r0 hr0 hf0 rfl
  let d1 := arrayDone d entries
  have htagpos : d1.tagPos≤8*d1.lookup.t := by
    have h := (arrayDone_cursors d entries).1
    change d1.tagPos=d.tagPos+8*entries.length at h
    change d1.tagPos≤8*d.lookup.t
    omega
  obtain ⟨base,hbase,hbf,_⟩ := LookupRuntime.reset_tags_run d1.lookup d1.tagPos htagpos
  have hbf' : base.final=LookupRuntime.usedCfg base.final.control d1.lookup 0 := by
    rw [LookupRuntime.usedCfg_zero,hbf]
    rfl
  obtain ⟨r1,hr1,hf1,_⟩ := lift_used LookupRuntime.resetTagProgram d1 d1.lookup 0 _ base hbase hbf'
  obtain ⟨n1,hn1,hp1⟩ := call_phase 8 9 d1 (tagsDone d1) _ r1 hr1 hf1 rfl
  let d2 := tagsDone d1
  obtain ⟨promote,hpromote,hpf,_⟩ := LookupRuntime.promote_run d2.lookup nextBits hnext hwidth hstate
  obtain ⟨r2,hr2,hf2,_⟩ := lift_lookup LookupRuntime.promoteProgram d2 {d2.lookup with state:=nextBits}
    _ promote rfl hpromote hpf
  obtain ⟨n2,hn2,hp2⟩ := call_phase 9 10 d2 (stateDone d2 nextBits) _ r2 hr2 hf2 rfl
  let d3 := stateDone d2 nextBits
  obtain ⟨r3,hr3,hf3,_⟩ := increment_run d3 hindex (by change 2*d.w≤d.cap; omega)
  have hf3' : r3.final=cfg r3.final.control (roundDone d entries nextBits) := by rw [hf3]; rfl
  obtain ⟨n3,hn3,hp3⟩ := call_phase 10 0 d3 (roundDone d entries nextBits) _ r3 hr3 hf3' rfl
  change n1≤12*d.lookup.t+2+1 at hn1
  change n2≤7*d.lookup.j+5+1 at hn2
  change n3≤4*d.w+2+1 at hn3
  exact ⟨n0+n1+n2+n3,by omega,((hp0.trans hp1).trans hp2).trans hp3⟩

end NearCubicWires.RepairOrdinary.TransitionWalk

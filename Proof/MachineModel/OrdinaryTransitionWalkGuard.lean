import Proof.MachineModel.OrdinaryTransitionWalkTerminal

/-! Successful literal claim checking is followed by a paid source return
before entering lookup. The emitted copy and both unary-driver endpoints are
those of the physical check, not newly supplied fields. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lift_exact {s : ℕ} (p : Machine 21 s) (d : Store) (e : LookupRuntime.Store)
    (q : Fin s) (fuel : ℕ) (base : ExecutionReceipt 21 s) (hp : d.tagPos=0)
    (hr : runFrom p fuel (LookupRuntime.cfg p.start d.lookup)=some base)
    (hf : base.final=LookupRuntime.cfg q e) :
    ∃ r,runFrom (RecoveryFocus.machine lookupSlots p) fuel (cfg p.start d)=some r ∧
      r.final=cfg q {d with lookup:=e,tagPos:=0} ∧ r.steps=base.steps := by
  obtain ⟨r,hrun,hrf,hrs⟩ := RecoveryFocus.run_config lookupSlots lookup_injective p
    (cfg p.start d).heads (cfg p.start d).tapes _ _ base hr
  have hin := lookup_place p.start d d.lookup 0
  rw [LookupRuntime.usedCfg_zero] at hin
  have hid : ({d with lookup:=d.lookup,tagPos:=0} : Store)=d := by rw [←hp]
  rw [hid] at hin
  rw [hin] at hrun
  refine ⟨r,hrun,?_,hrs⟩
  rw [hrf,hf]
  have hout := lookup_place q d e 0
  rw [LookupRuntime.usedCfg_zero] at hout
  exact hout

def guarded (d : Store) (bits : List Bool) : Store :=
  {d with lookup:={d.lookup with scanCopy:=frame bits},tagPos:=0}

theorem guard_prefix (d : Store) (pre bits tail : List Bool) (htag : d.tagPos=0)
    (hs : d.lookup.scans=pre++Streaming.marks bits++tail) (hp : d.lookup.scanPos=pre.length)
    (hl : bits.length=d.lookup.t) (hb : d.lookup.scanCopy.length≤2*d.lookup.t+1) :
    ∃ time≤7*d.lookup.t+6,Timed machine time
      (cfg (RecoveryCalls.code sizes 4 (programs 4).start) d)
      (cfg (RecoveryCalls.code sizes 6 (programs 6).start) (guarded d bits)) := by
  let copied : LookupRuntime.Store := {d.lookup with scanPos:=d.lookup.scanPos+2*d.lookup.t,scanCopy:=frame bits}
  let d1 : Store := {d with lookup:=copied,tagPos:=0}
  obtain ⟨base,hbase,hbf,_⟩ := LookupRuntime.ClaimGuard.full_run d.lookup pre bits tail hs hp hl hb
  obtain ⟨r0,hr0,hf0,_⟩ := lift_exact LookupRuntime.ClaimGuard.machine d copied 4 _ base htag hbase hbf
  have hf0' : r0.final=cfg r0.final.control d1 := by rw [hf0]; rfl
  obtain ⟨n0,hn0,hp0⟩ := call_phase 4 5 d d1 _ r0 hr0 hf0' (by rw [hf0]; rfl)
  obtain ⟨last,hlast,hlf,_⟩ := LookupRuntime.ClaimGuard.return_run copied
  have hreturned : ({copied with scanPos:=copied.scanPos-2*copied.t} : LookupRuntime.Store)=
      {d.lookup with scanCopy:=frame bits} := by
    dsimp only [copied]
    simp only [Nat.add_sub_cancel]
  rw [hreturned] at hlf
  obtain ⟨r1,hr1,hf1,_⟩ := lift_exact LookupRuntime.ClaimGuard.returnProgram d1
    {d.lookup with scanCopy:=frame bits} 3 _ last rfl hlast hlf
  have hf1' : r1.final=cfg r1.final.control (guarded d bits) := by rw [hf1]; rfl
  obtain ⟨n1,hn1,hp1⟩ := call_phase 5 6 d1 (guarded d bits) _ r1 hr1 hf1' rfl
  change n1≤3*d.lookup.t+2+1 at hn1
  exact ⟨n0+n1,by omega,hp0.trans hp1⟩

theorem frame_take_drop (bits : List Bool) (width : ℕ) :
    frame bits=Streaming.marks (bits.take width)++frame (bits.drop width) := by
  have h := Streaming.frame_append (bits.take width) (bits.drop width)
  rw [List.take_append_drop] at h
  exact h

end NearCubicWires.RepairOrdinary.TransitionWalk

import Proof.MachineModel.OrdinaryTransitionWalkSemantics

/-! Bounded rejecting branches. Truncated claim checks may leave their local
heads unrestored; the enclosing controller halts after writing false and does
not invoke lookup or reuse those failed fields. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk.RejectHeads
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reject_config (heads : Fin 42→ℕ) (tapes : Fin 42→List Bool) (flag : Bool)
    (hh : heads 41=0) (ht : tapes 41=[flag]) :
    ∃ r,runFrom clearProgram 1 (RecoveryCalls.restarted clearProgram heads tapes)=some r ∧
      r.final.heads 41=0 ∧ r.final.tapes 41=[false] ∧ r.steps=1 := by
  obtain ⟨base,hbase,hbt,hbh,hbs⟩ := LookupReadBit.clear_ready flag
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config clearSlots (by decide) LookupReadBit.clear heads tapes _ _ base hbase
  have hin : RecoveryFocus.config clearSlots heads tapes
      (initialConfiguration LookupReadBit.clear (fun _=>[flag]))=RecoveryCalls.restarted clearProgram heads tapes := by
    apply TransitionEvent.focused_eq clearSlots (by decide) (RecoveryCalls.restarted clearProgram heads tapes)
    · rfl
    · intro i; fin_cases i; exact hh.symm
    · intro i; fin_cases i; exact ht.symm
    · intro i _; rfl
    · intro i _; rfl
  rw [hin] at hr
  have hp : RecoveryFocus.pick clearSlots (41 : Fin 42)=some (0 : Fin 1) :=
    RecoveryFocus.pick_slot clearSlots (by decide) 0
  refine ⟨r,hr,?_,?_,hrs.trans hbs⟩
  · rw [hrf]
    simp only [RecoveryFocus.config,hp]
    exact hbh 0
  · rw [hrf]
    simp only [RecoveryFocus.config,hp,hbt]

theorem reject_any (heads : Fin 42→ℕ) (tapes : Fin 42→List Bool) (flag : Bool)
    (hh : heads 41=0) (ht : tapes 41=[flag]) :
    ∃ time≤2,∃ output,Timed machine time
      (controlConfig (RecoveryCalls.code sizes 11) (RecoveryCalls.restarted (programs 11) heads tapes)) output ∧
      machine.halted output.control=true ∧ output.heads 41=0 ∧ output.tapes 41=[false] := by
  obtain ⟨r,hr,hrh,hrt,hrs⟩ := reject_config heads tapes flag hh ht
  obtain ⟨hp,halted⟩ := prefix_of_run (programs 11) 1 _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next 11 ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next 11 r.final halted rfl
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  refine ⟨r.steps+1,by omega,RecoveryCalls.stopped sizes r.final.heads r.final.tapes,h,?_,hrh,hrt⟩
  simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]

theorem short_guard_tail (d : Store) (pre bits : List Bool) (htag : d.tagPos=0)
    (hs : d.lookup.scans=pre++frame bits) (hp : d.lookup.scanPos=pre.length)
    (hl : bits.length<d.lookup.t) (hb : d.lookup.scanCopy.length≤2*d.lookup.t+1) :
    ∃ time≤4*d.lookup.t+5,∃ output,Timed machine time
      (cfg (RecoveryCalls.code sizes 4 (programs 4).start) d) output ∧
      machine.halted output.control=true ∧ output.heads 41=0 ∧ output.tapes 41=[false] := by
  obtain ⟨base,hbase,hbc,_⟩ := LookupRuntime.ClaimGuard.short_run d.lookup pre bits hs hp hl hb
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config lookupSlots lookup_injective LookupRuntime.ClaimGuard.machine
    (cfg (0 : Fin 6) d).heads (cfg (0 : Fin 6) d).tapes _ _ base hbase
  have hin := lookup_place (0 : Fin 6) d d.lookup 0
  rw [LookupRuntime.usedCfg_zero] at hin
  have hid : ({d with lookup:=d.lookup,tagPos:=0} : Store)=d := by rw [←htag]
  rw [hid] at hin
  have hin' : RecoveryFocus.config lookupSlots (cfg (0 : Fin 6) d).heads (cfg (0 : Fin 6) d).tapes
      (LookupRuntime.cfg LookupRuntime.ClaimGuard.machine.start d.lookup)=cfg (0 : Fin 6) d := hin
  rw [hin'] at hr
  have hn : ¬∃j,lookupSlots j=(41 : Fin 42) := by
    rintro ⟨j,hj⟩
    have hv := congrArg (fun z : Fin 42=>z.val) hj
    change j.val=41 at hv
    omega
  have hpick : RecoveryFocus.pick lookupSlots (41 : Fin 42)=none := by simp only [RecoveryFocus.pick,dif_neg hn]
  have hhead : r.final.heads 41=0 := by rw [hrf]; simp only [RecoveryFocus.config,hpick]; rfl
  have htape : r.final.tapes 41=[d.countFlag] := by rw [hrf]; simp only [RecoveryFocus.config,hpick]; rfl
  obtain ⟨hpath,halted⟩ := prefix_of_run (programs 4) (4*d.lookup.t+2) _ r hr
  have hbody := RecoveryCalls.body_timed sizes programs 0 next 4 ⟨r.peakTapeCells,hpath⟩
  have hnext : next 4 r.final.control r.final.scanned=some 11 := by
    rw [hrf]
    change (if base.final.control.val=4 then some 5 else some 11)=some 11
    rw [hbc]
    rfl
  have hreturn := RecoveryCalls.return_step sizes programs 0 next 4 11 r.final halted hnext
  have hprefix := hbody.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hreturn)
  obtain ⟨last,hlast,output,hout,hstop,hzero,hfalse⟩ := reject_any r.final.heads r.final.tapes d.countFlag hhead htape
  have hsteps := runFrom_steps_le (programs 4) (4*d.lookup.t+2) _ r hr
  exact ⟨r.steps+1+last,by omega,output,hprefix.trans hout,hstop,hzero,hfalse⟩

end NearCubicWires.RepairOrdinary.TransitionWalk.RejectHeads

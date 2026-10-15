import Proof.MachineModel.OrdinaryTransitionWalkActions

/-! Fixed tape focuses transport the accepted lookup and array executions.
All inactive cursors, including the global append cursor, remain physical. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def lookupProgram := RecoveryFocus.machine lookupSlots LookupRuntime.machine
noncomputable def terminalProgram := RecoveryFocus.machine lookupSlots LookupRuntime.TerminalFlags.machine
noncomputable def guardProgram := RecoveryFocus.machine lookupSlots LookupRuntime.ClaimGuard.machine
noncomputable def returnProgram := RecoveryFocus.machine lookupSlots LookupRuntime.ClaimGuard.returnProgram
noncomputable def resetTagsProgram := RecoveryFocus.machine lookupSlots LookupRuntime.resetTagProgram
noncomputable def promoteProgram := RecoveryFocus.machine lookupSlots LookupRuntime.promoteProgram
noncomputable def arrayProgram := RecoveryFocus.machine arraySlots TransitionArrayReuse.machine

theorem lift_used {s : ℕ} (p : Machine 21 s) (d : Store) (e : LookupRuntime.Store)
    (pos fuel : ℕ) (base : ExecutionReceipt 21 s)
    (hr : runFrom p fuel (LookupRuntime.usedCfg p.start d.lookup d.tagPos)=some base)
    (hf : base.final=LookupRuntime.usedCfg base.final.control e pos) :
    ∃ r,runFrom (RecoveryFocus.machine lookupSlots p) fuel (cfg p.start d)=some r ∧
      r.final=cfg r.final.control {d with lookup:=e,tagPos:=pos} ∧ r.steps=base.steps := by
  obtain ⟨r,hrun,hrf,hrs⟩ := RecoveryFocus.run_config lookupSlots lookup_injective p
    (cfg p.start d).heads (cfg p.start d).tapes _ _ base hr
  rw [lookup_place] at hrun
  refine ⟨r,hrun,?_,hrs⟩
  rw [hrf,hf]
  have h := lookup_place base.final.control d e pos
  exact h

theorem lift_lookup {s : ℕ} (p : Machine 21 s) (d : Store) (e : LookupRuntime.Store)
    (fuel : ℕ) (base : ExecutionReceipt 21 s) (hp : d.tagPos=0)
    (hr : runFrom p fuel (LookupRuntime.cfg p.start d.lookup)=some base)
    (hf : base.final=LookupRuntime.cfg base.final.control e) :
    ∃ r,runFrom (RecoveryFocus.machine lookupSlots p) fuel (cfg p.start d)=some r ∧
      r.final=cfg r.final.control {d with lookup:=e,tagPos:=0} ∧ r.steps=base.steps := by
  apply lift_used p d e 0 fuel base
  · rw [hp,LookupRuntime.usedCfg_zero]
    exact hr
  · rw [LookupRuntime.usedCfg_zero]
    exact hf

theorem array_run (d : Store) (entries : List TransitionArray.Item)
    (tagPre tagTail scanPre scanTail : List Bool)
    (hvalid : ∀ e∈entries,TagMachine.valid true e.tag=true)
    (hheads : ∀ e∈entries,e.head+1<2^d.w)
    (hserial : d.serial+entries.length<2^(2*d.w)) (htape : d.tape+entries.length<2^d.w)
    (hback : d.head.difference.length≤2*d.w+1) (hcap : 4*d.w+3≤d.cap)
    (hC : TransitionArray.loopBudget d.w entries.length≤d.C)
    (ha : d.array=ZeroPadding.pad d.C (TransitionArray.fields d.w entries))
    (ho : d.arrayOut=List.replicate d.C false)
    (htag : d.lookup.tags=tagPre++Streaming.marks (TransitionArray.tags entries)++tagTail)
    (hpos : d.tagPos=tagPre.length)
    (hscan : d.lookup.scans=scanPre++Streaming.marks (TransitionArray.scans entries)++scanTail)
    (hcursor : d.lookup.scanPos=scanPre.length) :
    ∃ r,runFrom arrayProgram (TransitionArrayReuse.budget d.w d.C) (cfg arrayProgram.start d)=some r ∧
      r.final=cfg r.final.control (withArray d (TransitionArrayReuse.finished d.w d.cap (eventStore d) entries)
        (ZeroPadding.pad d.C (TransitionArray.nextFields d.w entries)) (List.replicate d.C false)) ∧
      r.steps≤TransitionArrayReuse.budget d.w d.C := by
  obtain ⟨base,hbase,hbf,hbs⟩ := TransitionArrayReuse.reuse_run d.w d.cap d.C entries (eventStore d)
    tagPre tagTail scanPre scanTail hvalid hheads hserial htape hback hcap hC htag hpos hscan hcursor
  rw [←ha,←ho] at hbase
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config arraySlots (by decide) TransitionArrayReuse.machine
    (cfg TransitionArrayReuse.machine.start d).heads (cfg TransitionArrayReuse.machine.start d).tapes _ _ base hbase
  have hi := array_place TransitionArrayReuse.machine.start d (eventStore d) d.array d.arrayOut
  have he : withArray d (eventStore d) d.array d.arrayOut=d := rfl
  rw [he] at hi
  rw [hi] at hr
  refine ⟨r,hr,?_,hrs.trans_le hbs⟩
  rw [hrf,hbf]
  exact array_place _ d _ _ _

end NearCubicWires.RepairOrdinary.TransitionWalk

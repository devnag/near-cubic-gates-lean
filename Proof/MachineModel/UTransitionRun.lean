import Proof.MachineModel.UTransitionMatched

/-! Execute the entire counted transition walk on the actual prepared U
endpoint. The same source x/choices determine both initialization and trace. -/
namespace NearCubicWires.RepairOrdinary.UTransition
open LocalBitMultitape RecoveryExecution SignedSortKey RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepared_run {s : ℕ} (raw witness : List Bool) (final : Configuration 139 s)
    (hp : UPrepared.Prepared raw witness final) :
    ∃ v word x bound padding choices m suffix,
      raw=VerifierInputFields.source word x bound padding ∧ UInputScalars.Guards raw x bound ∧
      decode raw.length word=some v ∧ word.length≤Nat.log 2 raw.length ∧
      witness=binary (ClockDyadicLedger.width raw.length) m++choices++suffix ∧
      x.length≤choices.length ∧ choices.length≤ClockDyadicLedger.limit raw.length ∧
      m≤choices.length ∧ choices.length=RadixSemantics.value bound ∧
      ∃ r,runFrom machine ((m+1)*TransitionWalk.cycleBudget (store raw witness v word x choices m))
        (entry (extended final).heads (extended final).tapes)=some r ∧
      r.steps≤2048*(PCPResourceLedger.events x.length choices.length m v.tapeCount+1)*
        (ClockDyadicLedger.width raw.length+word.length+1)^2 ∧
      r.final.scanned 156=TransitionWalk.accepted v
        (ClaimedTrace.view (initialConfiguration v.machine (v.inputTapes x choices))) m suffix ∧
      r.final.heads 156=0 ∧
      (∀ finalView events,TransitionWalk.evaluate v
        (ClaimedTrace.view (initialConfiguration v.machine (v.inputTapes x choices))) m suffix=some (finalView,events) →
        r.final.tapes 92=(store raw witness v word x choices m).out++
          MemoryInitialEmission.fields (2*ClockDyadicLedger.width raw.length)
            (2*ClockDyadicLedger.width raw.length+2) (ClockDyadicLedger.width raw.length)
            (2*x.length+2*choices.length+2) events ∧
          r.final.heads 92=(r.final.tapes 92).length) := by
  obtain ⟨base,v,word,c,hmeta⟩ := UPrepared.prepared_runtime_fields raw witness final hp
  obtain ⟨x,choices,hn,hB,hw,he⟩ := UPrepared.source_fields raw witness final hp
  obtain ⟨word1,bound,padding,m,suffix,hraw,hguards,hprefix,hm,hchoices,h1t,h1h,h74t,h74h⟩ := hw
  obtain ⟨x0,bound0,padding0,hraw0,_⟩ := hmeta.source
  have hword : word1=word := (UInputEntry.source_unique _ _ _ _ _ _ _ _ (hraw.symm.trans hraw0)).1
  rw [hword] at hraw
  have hN : 2≤raw.length := by
    rw [hraw]
    simp only [VerifierInputFields.source,List.length_append,frame_length]
    omega
  have hcode : (VerifierEncoding.code v).length≤Nat.log 2 raw.length := by
    rw [hmeta.inputMetadata.code_eq]
    exact hmeta.inputMetadata.code_bound
  let d := store raw witness v word x choices m
  let view := ClaimedTrace.view (initialConfiguration v.machine (v.inputTapes x choices))
  have hready : TransitionWalk.Ready d v view := TransitionWalk.initial_ready raw.length v
    (2*word.length) (frame witness) (2*(ClockDyadicLedger.width raw.length+choices.length)) x choices m
    hN hn hB hm hcode (by rw [hmeta.inputMetadata.code_eq]; omega)
  let pre := Streaming.marks (binary (ClockDyadicLedger.width raw.length) m++choices)
  have hsource : d.lookup.scans=pre++frame suffix := by
    change frame witness=pre++frame suffix
    rw [hprefix,Streaming.frame_append]
  have hpos : d.lookup.scanPos=pre.length := by
    simp [d,store,TransitionWalk.initialStore,TransitionWalk.initialLookup,pre,Streaming.marks_length,Nat.mul_add]
  obtain ⟨small,hsmall,hsmallSteps,hout⟩ := TransitionWalk.walk_run d v view hready pre suffix hsource hpos
  change runFrom TransitionWalk.machine ((m+1)*TransitionWalk.cycleBudget d)
    (TransitionWalk.cfg TransitionWalk.machine.start d)=some small at hsmall
  change TransitionWalk.Outcome d v view m suffix small.final at hout
  let pcap := physicalCapacity c word.length (ClockDyadicLedger.width raw.length)
    (UWalkCapacity.amount (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount))
  let lcap := logicalCapacity c word.length
  obtain ⟨r,hr,hs,hfields,_⟩ := run_of_matched d _ small hsmall (extended final).heads (extended final).tapes
    pcap lcap (matched_heads raw witness base final v word x choices c m hmeta h1h h74h he)
      (matched_tapes raw witness base final v word x choices c m hmeta h1t h74t he)
  have hflagHead : r.final.heads 156=0 := (hfields 41).1.trans hout.cursor
  have hflagTape : ZeroPadding.pad 1 (r.final.tapes 156)=small.final.tapes 41 := by
    simpa [pcap,lcap,slots,physicalCapacity,logicalCapacity] using (hfields 41).2
  have hflag : r.final.scanned 156=TransitionWalk.accepted v view m suffix := by
    have hread := congrArg (fun xs => readTapeBit xs 0) (hflagTape.trans hout.decision)
    rw [ZeroPadding.read_pad] at hread
    simpa [Configuration.scanned,hflagHead,readTapeBit] using hread
  have heventTape : r.final.tapes 92=small.final.tapes 33 := by
    simpa [pcap,lcap,slots,physicalCapacity,logicalCapacity] using (hfields 33).2
  have heventHead : r.final.heads 92=small.final.heads 33 := (hfields 33).1
  have hbound := TransitionWalk.initial_walk_budget raw.length v (2*word.length) (frame witness)
    (2*(ClockDyadicLedger.width raw.length+choices.length)) x choices m
  rw [hmeta.inputMetadata.code_eq] at hbound
  have hcost : r.steps≤2048*(PCPResourceLedger.events x.length choices.length m v.tapeCount+1)*
      (ClockDyadicLedger.width raw.length+word.length+1)^2 := by
    rw [hs]
    apply (runFrom_steps_le TransitionWalk.machine _ _ small hsmall).trans
    exact hbound
  refine ⟨v,word,x,bound,padding,choices,m,suffix,hraw,hguards,hmeta.inputMetadata.decoded,
    hmeta.inputMetadata.code_bound,hprefix,hn,hB,hm,hchoices,r,hr,hcost,hflag,hflagHead,?_⟩
  intro finalView events heval
  obtain ⟨ht,hh,_,_,_,_⟩ := hout.emitted finalView events heval
  exact ⟨heventTape.trans ht,heventHead.trans (hh.trans (congrArg List.length heventTape).symm)⟩

end NearCubicWires.RepairOrdinary.UTransition

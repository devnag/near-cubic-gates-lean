import Proof.MachineModel.OrdinaryTransitionWalkOutcomeStep

/-! Total counted execution of the fixed transition-walk machine on an
arbitrary remaining literal witness. Every exit is bounded, and every complete
walk produces exactly the chronological claimed-trace events. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem walk_timed (remaining : ℕ) (d : Store) (v : OrdinaryVerifier)
    (view : ClaimedTrace.View v.tapeCount v.stateCount) (hr : Ready d v view)
    (hremaining : d.m-d.index=remaining) (pre bits : List Bool)
    (hsource : d.lookup.scans=pre++frame bits) (hpos : d.lookup.scanPos=pre.length) :
    ∃ time≤(remaining+1)*cycleBudget d,∃ output,Timed machine time (cfg machine.start d) output ∧
      Outcome d v view remaining bits output := by
  induction remaining generalizing d view pre bits with
  | zero=>
    have hi : d.index=d.m := by have h:=hr.index_le; omega
    obtain ⟨r,hrun,hfinal,hsteps,_⟩ := terminal_run d v view.control hr.canonical hr.lookup.tags_zero hr.m_fit hi
      (by have h:=hr.capacity; omega) hr.lookup.position (by have h:=hr.lookup.capacity; omega)
      hr.lookup.flagQuery hr.lookup.flagCounter
    obtain ⟨hpath,_⟩ := prefix_of_run machine _ _ r hrun
    have htimed : Timed machine r.steps (cfg machine.start d) r.final := ⟨r.peakTapeCells,hpath⟩
    rw [hfinal] at htimed
    exact ⟨r.steps,by simpa only [Nat.zero_add,Nat.one_mul] using hsteps.trans (terminal_budget_le d),_,htimed,
      terminal_outcome d v view bits hr.canonical⟩
  | succ n ih=>
    have hi : d.index<d.m := by omega
    by_cases hfit : v.tapeCount≤bits.length
    · let reads := vector v.tapeCount bits
      let post := bits.drop v.tapeCount
      have hword : List.ofFn reads=bits.take v.tapeCount := vector_word _ _ hfit
      have hchunks : d.lookup.scans=pre++Streaming.marks (List.ofFn reads)++frame post := by
        rw [hsource,frame_take_drop bits v.tapeCount,←hword]
        simp only [List.append_assoc,post]
      cases hhalt:v.machine.halted view.control with
      | true=>
        obtain ⟨time,htime,output,hpath,hstop,hzero,hfalse⟩ := failed_round d v view reads hr hi (Or.inl hhalt) pre (frame post) hchunks hpos
        have he : evaluate v view (n+1) bits=none := by simp only [evaluate,if_pos hfit,hhalt,↓reduceIte]
        exact ⟨time,htime.trans (Nat.le_mul_of_pos_left _ (by omega)),output,hpath,
          outcome_none d v view (n+1) bits output he hstop hzero hfalse⟩
      | false=>
        cases ha:v.machine.rule view.control reads with
        | none=>
          obtain ⟨time,htime,output,hpath,hstop,hzero,hfalse⟩ := failed_round d v view reads hr hi (Or.inr ha) pre (frame post) hchunks hpos
          have he : evaluate v view (n+1) bits=none := by
            change v.machine.rule view.control (vector v.tapeCount bits)=none at ha
            simp only [evaluate,if_pos hfit,hhalt,Bool.false_eq_true,↓reduceIte,ha]
          exact ⟨time,htime.trans (Nat.le_mul_of_pos_left _ (by omega)),output,hpath,
            outcome_none d v view (n+1) bits output he hstop hzero hfalse⟩
        | some a=>
          obtain ⟨first,hfirst,firstPath⟩ := round_prefix d v view reads a hr hi hhalt ha pre (frame post) hchunks hpos
          let e := advanced d view reads a
          have hready : Ready e v (ClaimedTrace.advance view a) := advanced_ready d v view reads a hr hi
          have hremain : e.m-e.index=n := by
            have hindex := (advanced_counters d view reads a).2.1
            change e.index=d.index+1 at hindex
            change d.m-e.index=n
            omega
          have hlookup := advanced_lookup d view reads a
          have hsource' : e.lookup.scans=(pre++Streaming.marks (List.ofFn reads))++frame post := by
            rw [hlookup]
            exact hchunks
          have hpos' : e.lookup.scanPos=(pre++Streaming.marks (List.ofFn reads)).length := by
            rw [hlookup]
            change d.lookup.scanPos+2*v.tapeCount=_
            simp only [List.length_append,Streaming.marks_length,List.length_ofFn,hpos]
          obtain ⟨last,hlast,output,lastPath,lastOutcome⟩ := ih e (ClaimedTrace.advance view a) hready hremain
            (pre++Streaming.marks (List.ofFn reads)) post hsource' hpos'
          have hbudget : cycleBudget e=cycleBudget d := advanced_budget d view reads a
          rw [hbudget] at hlast
          have htotal : first+last≤(n+1+1)*cycleBudget d := by
            have h := Nat.add_le_add hfirst hlast
            nlinarith
          exact ⟨first+last,htotal,output,firstPath.trans lastPath,
            outcome_step d v view n bits a hr hfit hhalt ha output lastOutcome⟩
    · obtain ⟨first,hfirst,firstPath⟩ := test_prefix d hr.m_fit (hi.trans hr.m_fit) (by have h:=hr.capacity; omega)
      have hnode : testNode d=4 := by simp [testNode,Nat.not_le.mpr hi]
      rw [hnode] at firstPath
      have hshort : bits.length<d.lookup.t := by rw [hr.canonical.tapes_eq]; omega
      obtain ⟨last,hlast,output,lastPath,hstop,hzero,hfalse⟩ := RejectHeads.short_guard_tail (compared d) pre bits
        hr.lookup.tags_zero hsource hpos hshort hr.lookup.scanCopy
      change last≤4*d.lookup.t+5 at hlast
      obtain ⟨ht,_,_,_,_⟩ := hr.canonical.dimensions (fun _=>false)
      have htime : first+last≤cycleBudget d := by unfold cycleBudget; nlinarith
      have he : evaluate v view (n+1) bits=none := by rw [evaluate,if_neg hfit]
      exact ⟨first+last,htime.trans (Nat.le_mul_of_pos_left _ (by omega)),output,firstPath.trans lastPath,
        outcome_none d v view (n+1) bits output he hstop hzero hfalse⟩

theorem walk_run (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (hr : Ready d v view) (pre bits : List Bool)
    (hsource : d.lookup.scans=pre++frame bits) (hpos : d.lookup.scanPos=pre.length) :
    ∃ r,runFrom machine ((d.m-d.index+1)*cycleBudget d) (cfg machine.start d)=some r ∧
      r.steps≤(d.m-d.index+1)*cycleBudget d ∧ Outcome d v view (d.m-d.index) bits r.final := by
  obtain ⟨time,htime,output,hpath,hout⟩ := walk_timed (d.m-d.index) d v view hr rfl pre bits hsource hpos
  obtain ⟨r,hrun,hfinal,hsteps⟩ := hpath.run hout.halted
  have hm := runFrom_moreFuel machine _ ((d.m-d.index+1)*cycleBudget d-time) _ r hrun
  rw [Nat.add_sub_of_le htime] at hm
  exact ⟨r,hm,by omega,by rw [hfinal]; exact hout⟩

end NearCubicWires.RepairOrdinary.TransitionWalk

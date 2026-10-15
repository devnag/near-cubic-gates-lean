import Proof.MachineModel.OrdinaryTransitionWalkOutcome

/-! Output invariants compose across one physical transition and the
remaining counted walk, using the exact chronological serialization law. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem evaluate_step (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (n : ℕ) (bits : List Bool) (a : Action v.tapeCount v.stateCount)
    (hfit : v.tapeCount≤bits.length) (hhalt : v.machine.halted view.control=false)
    (ha : v.machine.rule view.control (vector v.tapeCount bits)=some a) :
    evaluate v view (n+1) bits=(evaluate v (ClaimedTrace.advance view a) n (bits.drop v.tapeCount)).map
      (fun result=>(result.1,MemoryTransition.batch view.heads (vector v.tapeCount bits)
        (fun i=>(a.write i).getD (vector v.tapeCount bits i))++result.2)) := by
  simp only [evaluate,if_pos hfit,hhalt,Bool.false_eq_true,↓reduceIte,ha]

theorem accepted_step (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (n : ℕ) (bits : List Bool) (a : Action v.tapeCount v.stateCount)
    (hfit : v.tapeCount≤bits.length) (hhalt : v.machine.halted view.control=false)
    (ha : v.machine.rule view.control (vector v.tapeCount bits)=some a) :
    accepted v view (n+1) bits=accepted v (ClaimedTrace.advance view a) n (bits.drop v.tapeCount) := by
  unfold accepted
  rw [evaluate_step v view n bits a hfit hhalt ha]
  cases evaluate v (ClaimedTrace.advance view a) n (bits.drop v.tapeCount) <;> rfl

theorem outcome_none (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (n : ℕ) (bits : List Bool) (output : Configuration 42 (Fintype.card (RecoveryCalls.Control sizes)))
    (he : evaluate v view n bits=none) (hh : machine.halted output.control=true)
    (hz : output.heads 41=0) (hb : output.tapes 41=[false]) : Outcome d v view n bits output := by
  refine ⟨hh,hz,?_,?_⟩
  · simpa only [accepted,he] using hb
  · intro finalView events h
    rw [he] at h
    cases h

theorem outcome_step (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (n : ℕ) (bits : List Bool) (a : Action v.tapeCount v.stateCount) (hr : Ready d v view)
    (hfit : v.tapeCount≤bits.length) (hhalt : v.machine.halted view.control=false)
    (ha : v.machine.rule view.control (vector v.tapeCount bits)=some a)
    (output : Configuration 42 (Fintype.card (RecoveryCalls.Control sizes)))
    (hnext : Outcome (advanced d view (vector v.tapeCount bits) a) v (ClaimedTrace.advance view a) n
      (bits.drop v.tapeCount) output) : Outcome d v view (n+1) bits output := by
  refine ⟨hnext.halted,hnext.cursor,?_,?_⟩
  · rw [accepted_step v view n bits a hfit hhalt ha]
    exact hnext.decision
  · intro finalView events he
    rw [evaluate_step v view n bits a hfit hhalt ha] at he
    cases htail:evaluate v (ClaimedTrace.advance view a) n (bits.drop v.tapeCount) with
    | none=>simp only [htail,Option.map_none] at he; cases he
    | some result=>
      obtain ⟨lastView,lastEvents⟩ := result
      have heq : (lastView,MemoryTransition.batch view.heads (vector v.tapeCount bits)
          (fun i=>(a.write i).getD (vector v.tapeCount bits i))++lastEvents)=(finalView,events) := by
        simpa only [htail,Option.map_some,Option.some.injEq] using he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj heq
      obtain ⟨hout,hhead,hserial,hserialHead,hstate,hstateHead⟩ := hnext.emitted lastView lastEvents htail
      let reads := vector v.tapeCount bits
      let batch := MemoryTransition.batch view.heads reads (fun i=>(a.write i).getD (reads i))
      have hs : (advanced d view reads a).serial=d.serial+v.tapeCount := (advanced_counters d view reads a).2.2.1
      refine ⟨?_,hhead,?_,hserialHead,?_,hstateHead⟩
      · change output.tapes 33=(advanced d view reads a).out++
          MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w (advanced d view reads a).serial lastEvents at hout
        rw [advanced_stream d v view reads a hr,hs] at hout
        change output.tapes 33=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial (batch++lastEvents)
        rw [MemoryInitialEmission.fields_append]
        have hb : batch.length=v.tapeCount := batch_length _ _ _
        rw [hb]
        simpa only [List.append_assoc] using hout
      · change output.tapes 31=binary (2*d.w) ((advanced d view reads a).serial+lastEvents.length) at hserial
        rw [hs] at hserial
        simp only [List.length_append,batch_length]
        simpa only [Nat.add_assoc] using hserial
      · rw [advanced_lookup] at hstate
        exact hstate

end NearCubicWires.RepairOrdinary.TransitionWalk

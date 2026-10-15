import Proof.MachineModel.OrdinaryTransitionWalkFailedRound

/-! Whole-walk output contract: the actual accept bit and chronological
stream/serial agree with the parsed symbolic trace on every complete walk. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Outcome (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (n : ℕ) (bits : List Bool) (output : Configuration 42 (Fintype.card (RecoveryCalls.Control sizes))) : Prop where
  halted : machine.halted output.control=true
  cursor : output.heads 41=0
  decision : output.tapes 41=[accepted v view n bits]
  emitted : ∀ finalView events,evaluate v view n bits=some (finalView,events) →
    output.tapes 33=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial events ∧
    output.heads 33=(output.tapes 33).length ∧
    output.tapes 31=binary (2*d.w) (d.serial+events.length) ∧ output.heads 31=0 ∧
    output.tapes 6=frame (binary d.lookup.j finalView.control.val) ∧ output.heads 6=0

theorem terminal_budget_le (d : Store) : 128*(d.lookup.code.length+1)^2+4*d.w+10≤cycleBudget d := by
  unfold cycleBudget
  nlinarith

theorem advanced_budget (d : Store) {t s : ℕ} (view : ClaimedTrace.View t s) (reads : Fin t→Bool) (a : Action t s) :
    cycleBudget (advanced d view reads a)=cycleBudget d := by
  unfold cycleBudget
  rw [advanced_lookup]
  rfl

theorem batch_length {t : ℕ} (heads : Fin t→ℕ) (reads after : Fin t→Bool) :
    (MemoryTransition.batch heads reads after).length=t := by simp [MemoryTransition.batch]

theorem advanced_stream (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (reads : Fin v.tapeCount→Bool) (a : Action v.tapeCount v.stateCount) (hr : Ready d v view) :
    (advanced d view reads a).out=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial
      (MemoryTransition.batch view.heads reads (fun i=>(a.write i).getD (reads i))) := by
  have h := roundDone_stream (looked d (List.ofFn reads)) (actionItems a view.heads reads)
    (binary d.lookup.j a.nextControl.val)
    (by intro e he; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he; have h:=hr.heads_fit i; change view.heads i<2^d.w; omega)
    (by change d.tape+(actionItems a view.heads reads).length<2^d.w
        rw [hr.tape_zero]
        simpa only [actionItems,List.length_ofFn,Nat.zero_add] using hr.tape_fit)
  change (advanced d view reads a).out=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial
    (itemEvents d.tape (actionItems a view.heads reads)) at h
  rw [hr.tape_zero,actionItems_events] at h
  exact h

theorem terminal_outcome (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (bits : List Bool) (hc : LookupRuntime.Canonical d.lookup v view.control) :
    Outcome d v view 0 bits (cfg (RecoveryCalls.controlCode sizes none) (terminalOut (compared d))) := by
  refine ⟨?_,rfl,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg]
  · change [d.lookup.code.getD (LookupRuntime.flagOffset d.lookup) false &&
      d.lookup.code.getD (LookupRuntime.flagOffset d.lookup+1) false]=[accepted v view 0 bits]
    rw [hc.halt_bit,hc.accept_bit]
    rfl
  · intro finalView events he
    have heq : (view,([] : List Event))=(finalView,events) := Option.some.inj he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj heq
    refine ⟨?_,rfl,?_,rfl,?_,rfl⟩
    · change d.out=d.out++MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial []
      simp [MemoryInitialEmission.fields,StablePartition.recordsBits]
    · rfl
    · change frame d.lookup.state=frame (binary d.lookup.j view.control.val)
      rw [hc.state_eq,hc.width_eq]

end NearCubicWires.RepairOrdinary.TransitionWalk

import Proof.PCP.VerifierDecodingWholeSemantics

/-! The guard has moved s and c to s+1 and e+1. These two actual scans
restore both to head1, preserving the code, start-state and all other fields. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.ReadyCounters
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine (CounterReset.program (2 : Fin 20))
  (CounterReset.program (3 : Fin 20))
noncomputable def input {a : ℕ} (base : Configuration 20 a) : Configuration 20 6 :=
  ⟨machine.start,base.heads,base.tapes⟩
def afterS {a : ℕ} (base : Configuration 20 a) : Configuration 20 3 :=
  ⟨2,(fun i => if i=2 then 1 else base.heads i),base.tapes⟩
def output {a : ℕ} (base : Configuration 20 a) : Configuration 20 6 :=
  ⟨5,(fun i => if i=3 then 1 else if i=2 then 1 else base.heads i),base.tapes⟩

theorem reset_run {a : ℕ} (base : Configuration 20 a) (c s e : ℕ)
    (hs : s ≤ c) (he : e≤c)
    (hsh : base.heads 2=s+1) (hch : base.heads 3=e+1)
    (hst : base.tapes 2=CapMachine.counter c s) (hct : base.tapes 3=CapMachine.counter c c) :
    ∃ r, runFrom machine (s+e+5) (input base)=some r ∧
      r.final=output base ∧ r.steps=s+e+5 := by
  obtain ⟨first,hfirst,hff,hft⟩ := CounterReset.reset_run (2 : Fin 20) base.heads base.tapes c s s
    hs (Nat.le_refl _) hst hsh
  obtain ⟨last,hlast,hlf,hlt⟩ := CounterReset.reset_run (3 : Fin 20) (afterS base).heads (afterS base).tapes
    c c e (Nat.le_refl _) he hct (by simpa [afterS] using hch)
  have hi : Composition.restart first.final (CounterReset.program (3 : Fin 20)).start=
      (⟨0,(afterS base).heads,(afterS base).tapes⟩ : Configuration 20 3) := by rw [hff]; rfl
  rw [←hi] at hlast
  have hj := Composition.run_join (CounterReset.program (2 : Fin 20)) (CounterReset.program (3 : Fin 20))
    (s+2) (e+2) _ first last hfirst hlast
  have htime : (s+2)+1+(e+2)=s+e+5 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 3 last.final=output base
    rw [hlf]
    rfl
  · change first.steps+1+last.steps=s+e+5
    omega

theorem endpoint_counters (word fields : List Bool) (limit t s x y : ℕ) (out : State) :
    (Whole.endpoint word fields limit t s x y out).heads 2=s+1 ∧
    (Whole.endpoint word fields limit t s x y out).heads 3=2^t*s+1 ∧
    (Whole.endpoint word fields limit t s x y out).tapes 2=CapMachine.counter word.length s ∧
    (Whole.endpoint word fields limit t s x y out).tapes 3=CapMachine.counter word.length word.length := by
  simp [Whole.endpoint,TableLayout.output,RecoveryFocus.config,TableLayout.slot_pick,
    RecoveryCalls.stopped,FrontTable.reset,FrontTable.guarded,TableGuardLayout.output,TableGuardLayout.slot_pick,
    Composition.rightConfig,TableBoundMachine.succeeded,TableBoundMachine.acceptOutput,
    TableBoundMachine.productOutput,TableBoundMachine.store]

theorem endpoint_reset (word fields : List Bool) (limit t s x y : ℕ) (out : State)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (he : 2^t*s ≤ word.length) :
    ∃ r, runFrom machine (s+2^t*s+5) (input (Whole.endpoint word fields limit t s x y out))=some r ∧
      r.final=output (Whole.endpoint word fields limit t s x y out) ∧ r.steps=s+2^t*s+5 ∧
      r.steps≤2*word.length+5 := by
  obtain ⟨hsh,hch,hst,hct⟩ := endpoint_counters word fields limit t s x y out
  have hlen := GuardedPreparation.parts_lengths hp
  obtain ⟨r,hr,hf,hs⟩ := reset_run (Whole.endpoint word fields limit t s x y out) word.length s (2^t*s)
    (by omega) he hsh hch hst hct
  exact ⟨r,hr,hf,hs,by omega⟩

end NearCubicWires.RepairSource.VerifierDecoding.ReadyCounters

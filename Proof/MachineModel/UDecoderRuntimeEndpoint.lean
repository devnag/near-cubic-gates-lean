import Proof.MachineModel.UDecoderRuntimeScalars

/-! Exact physical scalar fields retained by the decoder's ready endpoint.
The code-source equality is an explicit retained invariant; zero tails are
observational relations and do not allocate any new cells. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem padded_counter_unique (tape : List Bool) (a b c d t u : ℕ)
    (ht : ZeroPadding.pad a tape=CapMachine.counter c t)
    (hu : ZeroPadding.pad b tape=CapMachine.counter d u) : t=u := by
  have he (p : ℕ) : decide (p<t)=decide (p<u) := by
    rw [←CapMachine.counter_read c t p,←ht,ZeroPadding.read_pad,
      ←ZeroPadding.read_pad b tape (p+1),hu,CapMachine.counter_read]
  have ht' := he t
  have hu' := he u
  simp only [lt_self_iff_false,decide_false,Bool.false_eq,decide_eq_false_iff_not,not_lt] at ht' hu'
  omega

theorem ready_code_fields (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 0=out.pre.length ∧
    (Ready.endpoint word fields limit t s x y out).tapes 0=out.pre++frame out.bits := by
  simp [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,ReadyCounters.output,
    Whole.endpoint,TableLayout.output,RecoveryFocus.config,TableLayout.slot_pick,
    ZeroPadding.config,TableLayout.capacity,TableValidation.endpoint,RecordsDriver.cfg,
    TableValidation.finished,TableValidation.flagOutput,RecordsMachine.input,RecordMachine.cfg,
    Fin.addCases]

theorem ready_s_c (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 2=1 ∧
    (Ready.endpoint word fields limit t s x y out).heads 3=1 ∧
    (Ready.endpoint word fields limit t s x y out).tapes 2=CapMachine.counter word.length s ∧
    (Ready.endpoint word fields limit t s x y out).tapes 3=CapMachine.counter word.length word.length := by
  obtain ⟨_,_,hs,hc⟩ := ReadyCounters.endpoint_counters word fields limit t s x y out
  refine ⟨rfl,rfl,?_,?_⟩
  · simpa [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,ReadyCounters.output,
      Fin.addCases] using hs
  · simpa [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,ReadyCounters.output,
      Fin.addCases] using hc

theorem ready_bound (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 7=0 ∧
    (Ready.endpoint word fields limit t s x y out).tapes 7=frame (binary (natBitLength s) s) := by
  simp [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,ReadyCounters.output,
    Whole.endpoint,TableLayout.output,RecoveryFocus.config,TableLayout.slot_pick,
    ZeroPadding.config,TableLayout.capacity,TableValidation.endpoint,RecordsDriver.cfg,
    TableValidation.finished,TableValidation.flagOutput,RecordsMachine.input,RecordMachine.cfg,
    Fin.addCases,Front.bound,fixedBits_binary]

theorem ready_start (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 11=0 ∧
    (Ready.endpoint word fields limit t s x y out).tapes 11=frame (fields.take (natBitLength s)) := by
  simp [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,ReadyCounters.output,
    Whole.endpoint,TableLayout.output,RecoveryFocus.config,TableLayout.slot_pick,
    FrontTable.reset,FrontTable.guarded,TableGuardLayout.output,TableGuardLayout.slot_pick,
    FrontTable.front,TapeEmbedding.config,Front.endpoint,StartFlags.endpoint,FlagsLayout.output,
    StartLayout.output,StartLayout.input,Fin.addCases,Front.bound_length]

theorem ready_four_t (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 20=1 ∧
    (Ready.endpoint word fields limit t s x y out).tapes 20=CompareMachine.word (4*t) := by
  exact ⟨rfl,rfl⟩

theorem runtime_metadata_caps (word : List Bool) :
    Ready.inputCapacity word 0=0 ∧ Ready.inputCapacity word 1=word.length+2 ∧
    Ready.inputCapacity word 2=word.length+2 ∧ Ready.inputCapacity word 3=word.length+2 ∧
    Ready.inputCapacity word 7=0 ∧ Ready.inputCapacity word 10=0 ∧
    Ready.inputCapacity word 11=0 ∧ Ready.inputCapacity word 20=0 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.UDecoder

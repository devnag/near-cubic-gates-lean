import Proof.PCP.VerifierDecodingReady

/-! Physical t/j drivers of the accepted decoder. Zero tails are exposed
through the decoder's existing padding relation, never installed for free. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_t (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 1=1 ∧
    (Ready.endpoint word fields limit t s x y out).tapes 1=CapMachine.counter word.length t := by
  simpa [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,Fin.addCases] using
    ReadyLayout.endpoint_tape word fields limit t s x y out

theorem ready_j (word fields : List Bool) (limit t s x y : ℕ) (out : RecordsMachine.State) :
    (Ready.endpoint word fields limit t s x y out).heads 10=1 ∧
    (Ready.endpoint word fields limit t s x y out).tapes 10=CompareMachine.word (natBitLength s) := by
  simp [Ready.endpoint,RecoveryCalls.stopped,ReadyLayout.output,ReadyCounters.output,
    Whole.endpoint,TableLayout.output,RecoveryFocus.config,TableLayout.slot_pick,
    ZeroPadding.config,TableLayout.capacity,TableValidation.endpoint,RecordsDriver.cfg,
    TableValidation.finished,TableValidation.flagOutput,RecordsMachine.input,RecordMachine.cfg,
    Fin.addCases,Front.bound_length]

theorem runtime_scalar_caps (word : List Bool) : Ready.inputCapacity word 1=word.length+2 ∧
    Ready.inputCapacity word 10=0 := by
  constructor <;> rfl

end NearCubicWires.RepairOrdinary.UDecoder

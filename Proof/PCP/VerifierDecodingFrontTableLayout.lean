import Proof.PCP.VerifierDecodingTableLayout

/-! The actual front supplies the capped guard's entry; its exact successful
store then supplies every field of counted table validation after one paid
t-counter reset. The start-state word remains on its own retained tape. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.FrontTable
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extras (c : ℕ) : Fin 6 → List Bool :=
  ![List.replicate (c+2) false,List.replicate (c+2) false,List.replicate (c+2) false,[false],[],[false]]
noncomputable def front (word fields : List Bool) (limit t s x y : ℕ) :=
  TapeEmbedding.config (fun _ : Fin 6 => 0) (extras word.length)
    (Front.endpoint word fields limit t s x y)
noncomputable def guarded (word fields : List Bool) (limit t s x y : ℕ) :=
  TableGuardLayout.output (front word fields limit t s x y) word.length t s
noncomputable def reset (word fields : List Bool) (limit t s x y : ℕ) : Configuration 20 3 :=
  let g := guarded word fields limit t s x y
  ⟨2,(fun i => if i=1 then 1 else g.heads i),g.tapes⟩
def tablePre (fields : List Bool) (t s : ℕ) :=
  StartFlags.afterStart (StartLayout.headerPrefix t s) fields (Front.bound s)++
    Streaming.marks ((fields.drop (Front.bound s).length).take (2*s))
def tableState (fields : List Bool) (t s : ℕ) : State :=
  ⟨tablePre fields t s,fields.drop ((Front.bound s).length+2*s),[],true,false⟩

theorem guard_entry (word fields : List Bool) (limit t s x y : ℕ) :
    TableGuardLayout.Entry (front word fields limit t s x y) word.length t s := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> simp [TableGuardLayout.slot,front,extras,TapeEmbedding.config,Front.endpoint,
      StartFlags.endpoint,FlagsLayout.output,StartLayout.output,StartLayout.input,
      Dimensions.endpoint,PreparedWidth.output,GuardedPreparation.endpoint,GuardedPreparation.prepared,
      GuardedPreparation.extend,Preparation.finished,Preparation.cap,
      TableGuardLayout.localEntry,TableBoundEntry.capacity,TableBoundEntry.initial,TableBoundEntry.tapes,
      Composition.leftConfig,ZeroPadding.config,CapMachine.counter,CompareMachine.word,
      RecoveryCalls.stopped,Fin.addCases,ZeroPadding.pad]

theorem reset_run (word fields : List Bool) (limit t s x y : ℕ) (ht : t≤word.length) :
    ∃ r, runFrom (CounterReset.program (1 : Fin 20)) (t+2)
      ⟨0,(guarded word fields limit t s x y).heads,(guarded word fields limit t s x y).tapes⟩=some r ∧
      r.final=reset word fields limit t s x y ∧ r.steps=t+2 := by
  apply CounterReset.reset_run (1 : Fin 20) _ _ word.length t t ht (Nat.le_refl _)
  · simp [guarded,TableGuardLayout.output,RecoveryFocus.config,TableGuardLayout.slot_pick,
      Composition.rightConfig,TableBoundMachine.succeeded,RecoveryCalls.stopped,
      TableBoundMachine.acceptOutput,TableBoundMachine.store]
  · simp [guarded,TableGuardLayout.output,RecoveryFocus.config,TableGuardLayout.slot_pick,
      Composition.rightConfig,TableBoundMachine.succeeded,RecoveryCalls.stopped,
      TableBoundMachine.acceptOutput,TableBoundMachine.productOutput]

theorem table_source (word fields : List Bool) (t s : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) :
    frame word=(tableState fields t s).pre++frame (tableState fields t s).bits := by
  obtain ⟨hsource,_⟩ := StartLayout.header_source hp
  rw [hsource]
  have hsplit : Streaming.marks (fields.take (Front.bound s).length)++
      Streaming.marks ((fields.drop (Front.bound s).length).take (2*s))++
      frame (fields.drop ((Front.bound s).length+2*s))=frame fields := by
    rw [List.append_assoc,←List.drop_drop,←Streaming.frame_append,List.take_append_drop,
      ←Streaming.frame_append,List.take_append_drop]
  simpa only [tableState,tablePre,StartFlags.afterStart,List.append_assoc] using
    congrArg (fun z => StartLayout.headerPrefix t s++z) hsplit.symm

theorem table_entry (word fields : List Bool) (limit t s x y : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (hs : 0<s)
    (hv : StartFlags.valid fields (Front.bound s) s=true) :
    TableLayout.Entry (reset word fields limit t s x y) (Front.bound s) t word.length (2^t*s)
      (tableState fields t s) := by
  have hchecks : RecordMachine.rangeValid fields (Front.bound s) ∧
      2*s≤(fields.drop (Front.bound s).length).length := by simpa [StartFlags.valid] using hv
  have hstart := hchecks.1
  have hflags := hchecks.2
  have htake : (fields.take (Front.bound s).length).length=(Front.bound s).length := by
    simp [Nat.min_eq_left hstart.1]
  have hflagTake : ((fields.drop (Front.bound s).length).take (2*s)).length=2*s := by
    rw [List.length_take,Nat.min_eq_left hflags]
  have hsource := table_source word fields t s hp
  have hb := PreparedWidth.output_binary (GuardedPreparation.endpoint word limit t s) s x y hs
  have hwidth : BitWidthMachine.width s=(Front.bound s).length := by
    rw [Front.bound_length,BitWidthMachine.width_eq s hs]
  have hdimension : BitWidthMachine.dimension s=frame (Front.bound s) := hb.1
  constructor
  · intro i; fin_cases i <;> simp [reset,guarded,TableGuardLayout.output,RecoveryFocus.config,
      TableGuardLayout.slot_pick,TableLayout.slot,front,TapeEmbedding.config,Front.endpoint,
      StartFlags.endpoint,FlagsLayout.output,StartLayout.output,StartLayout.input,StartFlags.afterStart,
      tableState,tablePre,Streaming.marks_length,htake,hflagTake,
      TableLayout.localEntry,TableValidation.initial,ZeroPadding.config,Composition.leftConfig,
      controlConfig,RecordsDriver.cfg,input,RecordMachine.cfg,Fin.addCases,
      Composition.rightConfig,TableBoundMachine.succeeded,RecoveryCalls.stopped,
      TableBoundMachine.acceptOutput,TableBoundMachine.productOutput]
    all_goals first | rfl | omega
  · intro i; fin_cases i <;> simp [reset,guarded,TableGuardLayout.output,RecoveryFocus.config,
      TableGuardLayout.slot_pick,TableLayout.slot,front,TapeEmbedding.config,Front.endpoint,
      StartFlags.endpoint,FlagsLayout.output,StartLayout.output,StartLayout.input,extras,
      TableLayout.localEntry,TableValidation.initial,ZeroPadding.config,TableLayout.capacity,
      Composition.leftConfig,controlConfig,RecordsDriver.cfg,input,RecordMachine.cfg,Fin.addCases,
      Composition.rightConfig,TableBoundMachine.succeeded,RecoveryCalls.stopped,
      TableBoundMachine.acceptOutput,TableBoundMachine.store,CapMachine.counter,CompareMachine.word,
      tableState,Dimensions.endpoint,PreparedWidth.output,GuardedPreparation.endpoint,GuardedPreparation.prepared,
      ZeroPadding.pad,hwidth,hdimension]
    all_goals exact hsource

end NearCubicWires.RepairSource.VerifierDecoding.FrontTable

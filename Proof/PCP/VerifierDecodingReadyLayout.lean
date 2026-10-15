import Proof.PCP.VerifierDecodingFourfoldReady

/-! Last physical decoder handoff: preserve the validated twenty-tape store
while writing the new tag-width driver on tape20. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.ReadyLayout
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot : Fin 2 → Fin 21 := ![1,20]
theorem slot_injective : Function.Injective slot := by decide
theorem slot_pick (i : Fin 21) : RecoveryFocus.pick slot i=
    if i=1 then some 0 else if i=20 then some 1 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slot slot_injective 0
    | exact RecoveryFocus.pick_slot slot slot_injective 1
    | simp [RecoveryFocus.pick,slot]
noncomputable def machine := RecoveryFocus.machine slot FourfoldReady.machine
noncomputable def input {a : ℕ} (base : Configuration 20 a) : Configuration 21 13 :=
  ⟨machine.start,fun i => Fin.addCases base.heads (fun _ : Fin 1 => 0) i,
    fun i => Fin.addCases base.tapes (fun _ : Fin 1 => []) i⟩
def output {a : ℕ} (base : Configuration 20 a) (t : ℕ) : Configuration 21 13 :=
  ⟨12,fun i => Fin.addCases base.heads (fun _ : Fin 1 => 1) i,
    fun i => Fin.addCases base.tapes (fun _ : Fin 1 => CompareMachine.word (4*t)) i⟩

theorem width_run {a : ℕ} (base : Configuration 20 a) (c t : ℕ)
    (ht : t≤c) (hh : base.heads 1=1) (hsource : base.tapes 1=CapMachine.counter c t) :
    ∃ r, runFrom machine (9*t+9) (input base)=some r ∧
      r.final=output base t ∧ r.steps=9*t+9 := by
  obtain ⟨a,ha,hf,hs⟩ := FourfoldReady.ready_run c t ht
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config slot slot_injective FourfoldReady.machine
    (input base).heads (input base).tapes _ _ a ha
  have hi : RecoveryFocus.config slot (input base).heads (input base).tapes
      (FourfoldReady.initial c t)=input base := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,FourfoldReady.initial,
        Composition.leftConfig,FourfoldReady.input,Fin.addCases,hh]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,FourfoldReady.initial,
        Composition.leftConfig,FourfoldReady.input,Fin.addCases,hsource]
  rw [hi] at hr
  refine ⟨r,hr,?_,by omega⟩
  rw [hrf,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,output,Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot_pick,input,output,FourfoldReady.data,Fin.addCases,hsource]

theorem endpoint_tape (word fields : List Bool) (limit t s x y : ℕ) (out : State) :
    (ReadyCounters.output (Whole.endpoint word fields limit t s x y out)).heads 1=1 ∧
      (ReadyCounters.output (Whole.endpoint word fields limit t s x y out)).tapes 1=
        CapMachine.counter word.length t := by
  simp [ReadyCounters.output,Whole.endpoint,TableLayout.output,RecoveryFocus.config,TableLayout.slot_pick,
    ZeroPadding.config,TableLayout.capacity,TableValidation.endpoint,RecordsDriver.cfg,
    TableValidation.finished,TableValidation.flagOutput,RecordsMachine.input,RecordMachine.cfg,
    RecoveryCalls.stopped,Fin.addCases,CapMachine.counter,CompareMachine.word]

end NearCubicWires.RepairSource.VerifierDecoding.ReadyLayout

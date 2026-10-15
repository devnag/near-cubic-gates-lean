import Proof.MachineModel.UInitializedCalls

/-! Actual front-success to complete initialized event stream, with physical
memory configuration retained for the transition-walk continuation. -/
namespace NearCubicWires.RepairOrdinary.UInitialized
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initialization_tail (raw witness : List Bool) (base : Configuration 81 frontStates)
    (hp : UFront.Successful raw witness base) (hbit : base.scanned 79=true) :
    ∃ n final,n≤ initBudget raw+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (UInitializationAmbient.entry base)) final ∧
      machine.halted final.control=true ∧ final.scanned 79=true ∧ Prepared raw witness final := by
  obtain ⟨x,choices,hn,hB,hx,hc,last,localFinal,small,hlast,hls,hlf,hheads,htapes,hevents,hsmall⟩ :=
    UInitializationAmbient.entry_run raw base (UFront.initialization_fields raw witness base hp hbit)
  obtain ⟨n,hnsteps,hstop⟩ := stop_receipt sizes programs 0 next 1
    (UInitialization.budget (ClockDyadicLedger.width raw.length) x.length choices.length) _ last hlast (by rfl)
  have hb := initialization_budget raw x choices hn hB
  have hflag := (initialized_bit base localFinal).trans hbit
  have hflag' : last.final.scanned 79=true := by rw [hlf]; exact hflag
  refine ⟨n,_,by omega,hstop,?_,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa only [RecoveryCalls.stopped,Configuration.scanned] using hflag'
  · refine ⟨base,x,choices,localFinal,hp,hbit,hn,hB,hx,hc,?_,?_,⟨small,hheads,htapes,hsmall⟩,hevents⟩
    · exact congrArg Configuration.heads hlf
    · exact congrArg Configuration.tapes hlf

end NearCubicWires.RepairOrdinary.UInitialized

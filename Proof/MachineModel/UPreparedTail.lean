import Proof.MachineModel.UPreparedCalls

/-! The initialized machine's successful continuation executes the139t
bootstrap directly and retains its complete actual preparation invariant. -/
namespace NearCubicWires.RepairOrdinary.UPrepared
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bootstrap_tail (raw witness : List Bool) (base : Configuration 97 frontStates)
    (hp : UInitialized.Prepared raw witness base) (hbit : base.scanned 79=true) :
    ∃ n final,n ≤ bootstrapBudget raw+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (UWalkBootstrap.entry base)) final ∧
      machine.halted final.control=true ∧ final.scanned 79=true ∧ Prepared raw witness final := by
  obtain ⟨c,t,j,hc,ht,hj,htape,hjtape,last,hlast,hnum,hpres,harray,hheads,_⟩ := UWalkBootstrap.entry_run raw witness base hp
  obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 1
    (UWalkArray.budget (ClockDyadicLedger.width raw.length) t j) _ last hlast (by rfl)
  have hb := bootstrap_budget raw c t j hc ht hj
  have h79 : last.final.tapes 79=base.tapes 79 ∧ last.final.heads 79=base.heads 79 :=
    hpres 79 (by decide) (by decide) (by decide) (by decide)
  have hflag : last.final.scanned 79=true := by
    simpa only [Configuration.scanned,h79.1,h79.2] using hbit
  refine ⟨n,_,by omega,hstop,?_,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa only [RecoveryCalls.stopped,Configuration.scanned] using hflag
  · exact ⟨base,c,t,j,hp,hbit,hc,ht,hj,htape,hjtape,hnum,hpres,harray,hheads⟩

end NearCubicWires.RepairOrdinary.UPrepared

import Proof.Amplification.RecoveryRawViewWholeHandoff

/-! Concrete successful loop return and final empty-tail trace. These
boundaries keep the large fixed machine controllers opaque at composition. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RecoveryRawViewLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem success_call (total fuel : Nat) (x : Cursor) (initial : Configuration 66 loopStates)
    (first : ExecutionReceipt 66 loopStates)
    (hr : runFrom RecoveryRawViewLoop.machine fuel initial=some first)
    (hf : first.final=RepeatMachine.cfg 3 (source x) total 1) :
    ∃ n,n ≤ fuel+1 ∧ Timed machine n (controlConfig (RecoveryCalls.code sizes 0) initial)
      (controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryRawViewEnd.cfg x.data total RecoveryRawViewEnd.machine.start)) := by
  have hn : next 0 first.final.control first.final.scanned=some 1 := by
    change (if first.final.control=RepeatMachine.phaseCode bodyStates 3 then some (1 : Fin 2) else none)=some 1
    rw [hf]
    exact if_pos rfl
  have htrace := call_receipt sizes programs 0 next 0 1 fuel initial first hr hn
  obtain ⟨n,hn,h⟩ := htrace
  rw [hf] at h
  rw [end_restart] at h
  exact ⟨n,hn,h⟩

theorem end_trace (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    ∃ n,n ≤ 262144*(width+1)^2+3 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryRawViewEnd.cfg x.data total RecoveryRawViewEnd.machine.start))
      (RecoveryCalls.stopped sizes (RecoveryRawViewEnd.cfg (RecoveryRawViewEnd.tested x.data) total (0 : Fin 1)).heads
        (RecoveryRawViewEnd.cfg (RecoveryRawViewEnd.tested x.data) total (0 : Fin 1)).tapes) := by
  have htest := RecoveryRawViewEnd.test_run x.data total hx.1.2.1
  obtain ⟨last,hr,hf,_⟩ := htest
  have hstop := stop_receipt sizes programs 0 next 1 (RecoveryRawViewEnd.budget x.data) _ last hr (by rfl)
  obtain ⟨n,hn,h⟩ := hstop
  rw [hf] at h
  have hb := end_budget width word x hx
  exact ⟨n,by omega,h⟩

end NearCubicWires.RepairOrdinary.RecoveryRawViewWhole

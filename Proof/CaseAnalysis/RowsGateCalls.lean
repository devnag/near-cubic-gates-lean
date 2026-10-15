import Proof.CaseAnalysis.RowsGateLayout

/-! Bounded ready receipts enter and stop the same finite controller with
symbolic state counts. This avoids reducing its full decoder state type at
every physical join; the existing call/stop transitions are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateColdCalls
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {t k : ℕ} (sizes : Fin k → ℕ)
  (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
  (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))

theorem call (j l : Fin k) (fuel : ℕ) (input output : Fin t → List Bool)
    (h : ClockJoin.ReadyRun (programs j) fuel input output)
    (hn : ∀ q,next j q (fun i => readTapeBit (output i) 0)=some l) :
    ∃ time ≤ fuel+1,Timed (RecoveryCalls.machine sizes programs entry next) time
      (controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) input))
      (controlConfig (RecoveryCalls.code sizes l) (initialConfiguration (programs l) output)) := by
  obtain ⟨r,hr,rt,rh,_rs⟩ := h
  have scanned : r.final.scanned=(fun i => readTapeBit (output i) 0) := by
    funext i;simp only [Configuration.scanned,rt,rh]
  obtain ⟨time,ht,trace⟩ := call_receipt sizes programs entry next j l fuel _ r hr
    (by rw [scanned];exact hn _)
  have restarted : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes=
      initialConfiguration (programs l) output := by
    apply configuration_ext
    · rfl
    · exact funext rh
    · exact rt
  rw [restarted] at trace
  exact ⟨time,ht,trace⟩

theorem stop (j : Fin k) (fuel : ℕ) (input output : Fin t → List Bool)
    (h : ClockJoin.ReadyRun (programs j) fuel input output)
    (hn : ∀ q,next j q (fun i => readTapeBit (output i) 0)=none) :
    ∃ time ≤ fuel+1,Timed (RecoveryCalls.machine sizes programs entry next) time
      (controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) input))
      (RecoveryCalls.stopped sizes (fun _ => 0) output) := by
  obtain ⟨r,hr,rt,rh,_rs⟩ := h
  have scanned : r.final.scanned=(fun i => readTapeBit (output i) 0) := by
    funext i;simp only [Configuration.scanned,rt,rh]
  obtain ⟨time,ht,trace⟩ := stop_receipt sizes programs entry next j fuel _ r hr
    (by rw [scanned];exact hn _)
  have stopped : RecoveryCalls.stopped sizes r.final.heads r.final.tapes=
      RecoveryCalls.stopped sizes (fun _ : Fin t => 0) output := by
    apply configuration_ext
    · rfl
    · exact funext rh
    · exact rt
  rw [stopped] at trace
  exact ⟨time,ht,trace⟩

theorem finish (fuel time : ℕ) (input output : Fin t → List Bool)
    (trace : Timed (RecoveryCalls.machine sizes programs entry next) time
      (controlConfig (RecoveryCalls.code sizes entry) (initialConfiguration (programs entry) input))
      (RecoveryCalls.stopped sizes (fun _ => 0) output)) (ht : time ≤ fuel) :
    ClockJoin.ReadyRun (RecoveryCalls.machine sizes programs entry next) fuel input output := by
  obtain ⟨r,hr,rf,rs⟩ := trace.run (by simp only [RecoveryCalls.machine,RecoveryCalls.stopped,
    Equiv.symm_apply_apply,Option.isNone_none])
  have more := runFrom_moreFuel (RecoveryCalls.machine sizes programs entry next) time (fuel-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨r,more,by rw [rf];rfl,by intro i;rw [rf];rfl,rs.le.trans ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateColdCalls

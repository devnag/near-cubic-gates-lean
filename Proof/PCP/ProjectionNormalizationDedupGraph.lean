import Proof.PCP.ProjectionNormalizationDedupCalls

/-! Every edge of the finite keep-last call graph is one executed transition.
These rules consume the focused callee receipts on the same physical store. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem call_phase (j k : Fin 6) (d e : Store) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 12 (sizes j)) (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : next j q (cfg q e).scanned=some k) :
    Timed body (r.steps+1) (atNode j d) (atNode k e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel (cfg (programs j).start d) r hr
  have ht := RecoveryCalls.body_timed sizes programs 0 next j (show Timed (programs j) r.steps _ _ from ⟨_,hp⟩)
  rw [hf] at ht hh
  have ret := Timed.single
    (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next j k (cfg q e) hh hn)
  exact ht.trans ret

theorem stop_phase (j : Fin 6) (d e : Store) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 12 (sizes j)) (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : next j q (cfg q e).scanned=none) :
    Timed body (r.steps+1) (atNode j d) (stopped e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel (cfg (programs j).start d) r hr
  have ht := RecoveryCalls.body_timed sizes programs 0 next j (show Timed (programs j) r.steps _ _ from ⟨_,hp⟩)
  rw [hf] at ht hh
  have ret := Timed.single
    (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.stop_step sizes programs 0 next j (cfg q e) hh hn)
  exact ht.trans ret

theorem stopped_halted (d : Store) : body.halted (stopped d).control=true := by
  simp [body,stopped,cfg,RecoveryCalls.machine,RecoveryCalls.controlCode]

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup

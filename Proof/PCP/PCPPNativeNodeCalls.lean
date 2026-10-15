import Proof.PCP.PCPPNativeNodeMachine

/-! Executed call/return edges for the one native-node controller. This
uses actual receipts and controls; no prepared tape vector is replaced at
a return and every call/stop transition costs its real extra step. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def boundary (j : Fin 21) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (RecoveryCalls.restarted (programs j) heads data)

theorem call_run (j l : Fin 21) (fuel : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (r : ExecutionReceipt 119 (sizes j))
    (hr : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) heads data)=some r)
    (hn : next j r.final.control r.final.scanned=some l) :
    Timed machine (r.steps+1) (boundary j heads data) (boundary l r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have body := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have ret := RecoveryCalls.return_step sizes programs 0 next j l r.final hh hn
  exact body.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret)

theorem stop_run (j : Fin 21) (fuel : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool)
    (r : ExecutionReceipt 119 (sizes j))
    (hr : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) heads data)=some r)
    (hn : next j r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (boundary j heads data) (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have body := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have ret := RecoveryCalls.stop_step sizes programs 0 next j r.final hh hn
  exact body.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret)

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine

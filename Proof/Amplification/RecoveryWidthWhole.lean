import Proof.Amplification.RecoveryWidth

/-! Whole physical canonical-width extension, including the empty input.
The entry count is the output of the existing cold length scanner. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdWidth
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem positive_entry (n : Nat) (hn : 0<n) : step machine (cfg 0 n 1)=some (cfg 1 n 1) := by
  have hm := mark n 0 hn
  simp [step,machine,cfg,Configuration.scanned,hm]
  rfl

theorem zero_entry : step machine (cfg 0 0 1)=some (cfg 2 1 2) := rfl

theorem width_trace (n : Nat) : Timed machine (2*n+6) (cfg 0 n 1) (cfg 5 (width n) 1) := by
  cases n with
  | zero=>
    exact ((Timed.single (by rfl) zero_entry).trans (append_trace 1)).trans (back_trace 3 2 (by omega))
  | succ n=>
    have h := (((Timed.single (by rfl) (positive_entry (n+1) (by omega))).trans
      (scan_trace (n+1) 0 (n+1) (by omega))).trans (append_trace (n+1))).trans
      (back_trace (n+3) (n+2) (by omega))
    have hw : width (n+1)=n+3 := by unfold width; rw [Nat.max_eq_right (by omega)]
    rw [hw]
    have he : 1+(n+1+1)+2+(n+2+1)=2*(n+1)+6 := by omega
    rw [he] at h
    exact h

theorem width_run (n : Nat) :
    ∃ r,runFrom machine (2*n+6) (cfg 0 n 1)=some r ∧
      r.final=cfg 5 (width n) 1 ∧ r.steps=2*n+6 :=
  (width_trace n).run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryColdWidth

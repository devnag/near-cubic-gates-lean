import Proof.MachineModel.OrdinarySourceSATLiftParse

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem quiet_trace {o : ℕ → Bool} {t : ℕ} (ports : Ports t) (piece : Piece t)
    (hq : ∀ q,piece.query q=none) (fuel : ℕ) (c : Configuration t piece.states)
    (r : ExecutionReceipt t piece.states) (hr : runFrom piece.machine fuel c=some r) :
    OrdinaryOracleTrace o (ports.program piece) r.steps c r.final := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact .refl _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact .refl _
    · next hh =>
      cases hs : step piece.machine c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom piece.machine fuel d with
        | none => simp [hs,ht] at hr
        | some tail =>
          simp only [hs,ht,Option.some.injEq] at hr
          subst r
          have hlocal : OrdinaryOracleStep o (ports.program piece) 1 c d :=
            OrdinaryOracleStep.local (program := ports.program piece) c d
              (by simpa [Ports.program] using hh) (hq c.control) hs
          simpa only [Nat.add_comm] using OrdinaryOracleTrace.cons hlocal (ih d tail ht)

theorem run_call (p : OrdinaryOracleProgram) (j k : Fin 7) (budget : ℕ)
    (heads afterHeads : Fin (tapes p) → ℕ) (data afterData : Fin (tapes p) → List Bool)
    (r : ExecutionReceipt (tapes p) (pieces p j).states)
    (hr : runFrom (pieces p j).machine budget ⟨(pieces p j).machine.start,heads,data⟩=some r)
    (hh : r.final.heads=afterHeads) (ht : r.final.tapes=afterData) (hs : r.steps ≤ budget)
    (hq : ∀ q,(pieces p j).query q=none)
    (hn : next p j r.final.control r.final.scanned=some k) :
    Path p j k (budget+1) heads afterHeads data afterData := by
  have h := call_trace p j k _ budget heads data r.final
    (quiet_trace (ports p) (pieces p j) hq budget _ r hr) (prefix_of_run _ _ _ r hr).2 hs hn
  rw [hh,ht] at h
  exact h

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full

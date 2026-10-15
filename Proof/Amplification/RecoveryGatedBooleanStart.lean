import Proof.Amplification.RecoveryOuterRootContinuation

/-! Explicit start-state form of the actual Boolean gate. The finite
control injection is discharged before instantiating large table graphs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryGatedSequence
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem boolean_start_run {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t)
    (b1 b2 : Nat) (heads : Fin t → Nat) (tapes : Fin t → List Bool) (first : ExecutionReceipt t s)
    (gate answer : Bool)
    (hr : runFrom p b1 ⟨p.start,heads,tapes⟩=some first) (hh : first.final.heads slot=0)
    (ht : first.final.tapes slot=[gate])
    (hreject : gate=false → answer=false)
    (hnext : gate=true → ∃ last,
      runFrom q b2 (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last ∧
      last.final.heads slot=0 ∧ last.final.tapes slot=[answer]) :
    ∃ r,runFrom (machine p q slot) (b1+b2+2)
        ⟨(machine p q slot).start,heads,tapes⟩=some r ∧
      r.steps ≤ b1+b2+2 ∧ r.final.heads slot=0 ∧ r.final.tapes slot=[answer] := by
  exact boolean_run p q slot b1 b2 ⟨p.start,heads,tapes⟩ first gate answer hr hh ht hreject hnext

end NearCubicWires.RepairOrdinary.RecoveryGatedSequence

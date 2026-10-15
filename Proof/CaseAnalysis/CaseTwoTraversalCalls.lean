import Proof.CaseAnalysis.CaseTwoTraversalFinish

/-! Specialize the finite call boundary before the enclosing list induction;
the node worker's state cardinality remains opaque in that induction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_call (fuel : ℕ) (H H' : Fin 30→ℕ) (A A' : Fin 30→List Bool)
    (r : ExecutionReceipt 30 _)
    (hr : runFrom node fuel ⟨node.start,H,A⟩=some r)
    (hh : r.final.heads=H') (ht : r.final.tapes=A') :
    Timed machine (r.steps+1) (cfg 1 H A) (cfg 0 H' A') :=
  call 1 0 fuel H H' A A' r hr hh ht (by intro q;rfl)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal

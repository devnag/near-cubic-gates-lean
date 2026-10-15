import Proof.Hierarchy.CompetitorSelectedRequestCountDock

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_run (r : Request) (Q : ℕ) (xs : List (Bool × ℕ))
    (hn : xs.length≤r.U*r.U) (hx : ∀ x∈selected xs,x<2^Q) : ∃ actual,
    run machine (budget r Q) (input r Q xs)=some actual ∧ actual.steps≤budget r Q ∧
      actual.final.heads=outputHeads Q (r.U*r.U) ∧
      actual.final.tapes 86=frame (binary (scalarWidth r Q) (selected xs).sum) ∧
      actual.final.tapes 76=List.replicate (scalarWidth r Q) true ∧
      actual.final.tapes 0=MatrixScoreBatch.physicalInput r := by
  obtain ⟨out,ho,h0,ht⟩ := CompetitorSelectedRequestDrivers.drivers_run r Q
  let ambient : Fin 91 → List Bool := Fin.addCases (m := 78) (n := 13)
    (motive := fun _ => List Bool) out (extra Q xs)
  have hp : ClockJoin.ReadyRun first (CompetitorSelectedRequestDrivers.budget r Q)
      (input r Q xs) ambient := ClockJoin.lift (e := 13) (Equiv.refl (Fin 91)) _ _ _ _ (extra Q xs) ho
  exact dock first (CompetitorSelectedRequestDrivers.budget r Q) r Q xs hn hx
    (input r Q xs) out hp h0 ht

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount

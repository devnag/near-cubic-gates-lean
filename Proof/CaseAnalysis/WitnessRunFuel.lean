import Proof.Foundations.OrdinaryMachine

/-! Fuel monotonicity is specialized before a large physical machine is
substituted, so consumers need no rewriting inside its receipt type. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RunFuel
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem enlarge {t s small large : ℕ} {p : Machine t s}
    {input : Fin t → List Bool} {r : ExecutionReceipt t s}
    (hr : run p small input=some r) (hb : small ≤ large) :
    run p large input=some r := by
  have more:=run_moreFuel p small (large-small) input r hr
  rw [Nat.add_sub_of_le hb] at more
  exact more

end NearCubicWires.RepairOrdinary.CloseoutWitness.RunFuel

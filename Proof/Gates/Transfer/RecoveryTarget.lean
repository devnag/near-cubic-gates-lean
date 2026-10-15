import Proof.Gates.Transfer.Frontier

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.RepairSource NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ}

/-- The closure with its source onset raised to `o`; every other field is unchanged. -/
noncomputable def withOnset (c : GateClosure s P ε) (o : ℕ) : GateClosure s P ε :=
  { c with g := { c.g with sourceOnset := o }, ready := { c.ready with } }

/-- **The `E^NP` recovery.** Every closure satisfies `RecoveryPart` after raising its source onset. -/
def RecoverySupply : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ) (c : GateClosure s P ε),
    ∃ o, c.g.sourceOnset ≤ o ∧ RecoveryPart (withOnset c o)

/-- The transfer side from the recovery. -/
theorem frontierOfClosure_of_recoverySupply (h : RecoverySupply) : FrontierOfClosure := by
  intro s P ε hε _ c
  obtain ⟨o, _, hrec⟩ := h s P ε c
  exact frontier_of_parts (withOnset c o) (schedulePart _) (caseOnePart _ hε) (caseTwoPart _) hrec

/-- With the weak-machine side, the whole `FrontierSupply`. -/
theorem frontierSupply_of_recoverySupply (h : RecoverySupply) (hsupply : ClosureSupply) :
    NearCubicGates.Close.FrontierSupply :=
  frontierSupply_of (frontierOfClosure_of_recoverySupply h) hsupply

end NearCubicGates.Close.Transfer

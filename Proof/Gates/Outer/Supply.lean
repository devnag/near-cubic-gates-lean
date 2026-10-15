import Proof.Gates.Outer.Interface

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.RepairSource

/-- lem:succinct-verifier for every clock exponent, hierarchy and `G`. -/
def SuccinctSupply : Prop :=
  ∀ (k : ℕ) (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ), Nonempty (SuccinctVerifier H G)

end NearCubicGates.Close.Outer

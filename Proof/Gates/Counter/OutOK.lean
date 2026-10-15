import Proof.Gates.Counter.Den

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open NearCubicGates.Close.Interfaces

/-- The printed interval of every (call, witness word) has length polynomial in the call's `n`. -/
def OutOK {B1 B2 : ℕ} (ctr : Interfaces.Counter B1 B2) : Prop :=
  ∃ C e : ℕ, ∀ (c : Call) (w : List Bool), (outputWord (ctr.value c w)).length ≤ C * (c.n + 1) ^ e

end NearCubicGates.Close.Counter

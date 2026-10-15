import Proof.Gates.Transfer.CaseOne
import Proof.Gates.Transfer.CaseTwo

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicGates.Close.Gadget

theorem frontierOfClosure_of_recovery
    (hrec : ∀ (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ), 0 < ε → ∀ c : GateClosure s P ε, RecoveryPart c) :
    FrontierOfClosure :=
  frontierOfClosure_of_parts fun s P ε hε _ c =>
    ⟨schedulePart c, caseOnePart c hε, caseTwoPart c, hrec s P ε hε c⟩

end NearCubicGates.Close.Transfer

import Proof.Gates.Dispatch.Main
import Proof.Gates.Dispatch.Witness

set_option autoImplicit false

namespace NearCubicGates.Close.Dispatch

open NearCubicGates.Close.Interfaces.Formats

noncomputable def dispatchMachineFinal (B1 B2 cT : ℕ) : DispatchMachine B1 B2 cT :=
  dispatchMachine B1 B2 cT witFrag

end NearCubicGates.Close.Dispatch

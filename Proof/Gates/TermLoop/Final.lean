import Proof.Gates.TermLoop.Main
import Proof.Gates.TermLoop.Exit
import Proof.Gates.TermLoop.Gadget7

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

theorem termLoop_ideal : TermLoopIdeal D ctr hct ω := termLoop_ideal_of D ctr hct ω (gadget_ideal D ctr hct ω)

theorem w3d (hD : Counter.DenOK ctr) : TermLoopIdeal D ctr hct ω ∧ LoopExitVI D ctr ω hD :=
  ⟨termLoop_ideal D ctr hct ω, loopExit_vi D ctr ω hD⟩

end NearCubicGates.Close.TermLoop

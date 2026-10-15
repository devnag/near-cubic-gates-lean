import Proof.Gates.Setup.Uniform
import Proof.Gates.OuterM.Width
import Proof.Gates.OuterM.ARun
import Proof.Gates.Setup.CompU

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicGates.Close NearCubicGates.Close.Transfer
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget

theorem setupSupply_of (hC : ∀ (s : GateSources) (P : ThreeQueryPCPP), CompU s P) : SetupSupply :=
  fun s P => setupU_of s P (hC s P) (fun g => OuterM.widthDonor s.mw (g.sv s)) (fun g => OuterM.aRun s.mw (g.sv s))

theorem setupSupply_of_subst (h : Succinct.SubstMachine.SubstReadySpec) : SetupSupply :=
  setupSupply_of (fun s P => compU_of h s P)

end NearCubicGates.Close.Setup

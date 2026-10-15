import Proof.Gates.Main.Chain
import Proof.Gates.Gadget.ThreeQuery
import Proof.Gates.HeadlineAssembly

set_option autoImplicit false

namespace NearCubicGates.Close

open NearCubicGates.HeadlineAssembly NearCubicGates.Close.Gadget

def FrontierSupply : Prop :=
  ∀ (_s : GateSources) (P : ThreeQueryPCPP), ∀ ε : ℝ, 0 < ε → ε < (P.gamma : ℝ) / 5 →
    Nonempty (NativeFrontier (P.gamma : ℝ) ε)

theorem main_from_inputs_of_frontier (hF : FrontierSupply) (hs : Outer.SuccinctSupply) : FinalStatement := by
  intro inputs
  have s := gateSources_of_inputs inputs hs
  obtain ⟨P⟩ := threeQuery_of_source s.threeQueryPCPP
  exact mainStatement_of_native_frontier P.gamma P.gamma_pos P.gamma_lt_one (hF s P)

end NearCubicGates.Close

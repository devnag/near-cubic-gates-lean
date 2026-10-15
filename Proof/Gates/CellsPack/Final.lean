import Proof.Gates.CellsPack.Cls2

set_option autoImplicit false

namespace NearCubicGates.Close.CellsPack

open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

theorem cellsUniform_of_loop : PackGoal := by
  intro S mainP K e hL B1 B2
  obtain ⟨Cc, E, hcls⟩ := budget_class S K e B1 B2
  exact ⟨fun cT => ⟨_, machOf S mainP K e hL B1 B2 (bigOf B1 B2) (fun _ r => cellN_bits_le r) (zOf S B1 B2)
    (zOf_ok S B1 B2) cT, ⟨Cc, E, fun r => hcls cT r⟩⟩, E, fun cT => ⟨Cc, fun r => hcls cT r⟩⟩

end NearCubicGates.Close.CellsPack

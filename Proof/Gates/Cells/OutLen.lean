import Proof.Wire_3_5.UnionMachineThrUnitIface4
import Proof.Foundations.OrdinaryRewindCarrier

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

theorem wf_out_len {Req : Type} {inp out : Req → List Bool} {bud : Req → ℕ} (f : WordFunction Req inp out bud)
    (r : Req) : (out r).length ≤ bud r + 1 := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes r
  have hp := (prefix_of_run _ _ _ _ hrun).1
  have hs := runFrom_steps_le _ _ _ _ hrun
  rw [← hout]
  refine NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit.prefix_len hp f.program.outputTape (bud r + 1) ?_ ?_
  · show (f.program.inputTapes (inp r) f.program.outputTape).length ≤ _
    simp [Program.inputTapes, f.program.outputFresh]
  · show 0 + receipt.steps ≤ _
    omega

end NearCubicGates.Close.Cells

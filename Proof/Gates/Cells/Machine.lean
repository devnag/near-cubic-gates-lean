import Proof.Gates.Cells.CostCls
import Proof.Gates.CellsPack.Final

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem cellsMachine_uniform (S : SolveMachine) (cP gP sP : St VV MM) (tc tg : Ctx → Call → Params → ℕ → ℕ)
    (ts : SolveMachine → Ctx → Call → Params → ℕ → ℕ)
    (hC : ConstGoal cP tc) (hCc : ConstClass tc) (hG : GatherGoal gP tg) (hGc : GatherClass tg)
    (hS : SysGoal sP ts) (hSc : SysClass ts) : ∀ B1 B2 : ℕ, CellsUniform B1 B2 := by
  obtain ⟨K, e, h⟩ := cellsLoopGoal S cP gP sP tc tg ts hC hCc hG hGc hS hSc
  exact NearCubicGates.Close.CellsPack.cellsUniform_of_loop S (mainOf cP gP sP) K e h

end NearCubicGates.Close.Cells

import Proof.Gates.Closure.Main
import Proof.Gates.CounterAsm.Main
import Proof.Gates.CounterMachine.Supply
import Proof.Gates.WorkerArith.Supply
import Proof.Gates.CellsPack.Final
import Proof.Gates.Expand.PolyTabDone
import Proof.Gates.CounterMachine.CellTablesMachine
import Proof.Gates.Solve.Machine
import Proof.Gates.Cells.Machine
import Proof.Gates.CellsSys.Final
import Proof.Gates.Recovery.Common

set_option autoImplicit false

namespace NearCubicGates.Close

theorem main_of_producers (hK5 : CounterMachine.Supply.PolyTabReady)
    (hK6 : ∀ B1 B2, CounterMachine.CellTablesUniform B1 B2) (S : Interfaces.Formats.SolveMachine) (mainP : Cells.St Cells.VV Cells.MM)
    (K e : ℕ) (hL : Cells.LoopGoal mainP S K e) (hSU : Setup.SetupSupply) (hR : Transfer.RecoverySupply) :
    NineFinalStatement :=
  Closure.final_of_machines
    (CounterAsm.counterSupply_of (CounterMachine.Supply.counterInputsAll_of hK5 hK6
      (fun B1 B2 => CellsPack.cellsUniform_of_loop S mainP K e hL B1 B2)))
    (WorkerArith.workerSupply hSU) hR

theorem main_of_loop (mainP : Cells.St Cells.VV Cells.MM) (K e : ℕ)
    (hL : Cells.LoopGoal mainP Solve.solveMachine K e) (hSU : Setup.SetupSupply) (hR : Transfer.RecoverySupply) :
    NineFinalStatement :=
  main_of_producers Expand.polyTabReady CounterMachine.cellTablesUniform Solve.solveMachine mainP K e hL hSU hR

theorem main_of_fragments (cP gP : Cells.St Cells.VV Cells.MM) (tc tg : Cells.Ctx → Interfaces.Call → Counter.Params → ℕ → ℕ)
    (hC : Cells.ConstGoal cP tc) (hCc : Cells.ConstClass tc) (hG : Cells.GatherGoal gP tg)
    (hGc : Cells.GatherClass tg) (hSU : Setup.SetupSupply) (hR : Transfer.RecoverySupply) : NineFinalStatement :=
  Closure.final_of_machines
    (CounterAsm.counterSupply_of (CounterMachine.Supply.counterInputsAll_of Expand.polyTabReady CounterMachine.cellTablesUniform
      (Cells.cellsMachine_uniform Solve.solveMachine cP gP Cells.SystemsPhase.sysP tc tg Cells.SystemsPhase.sysCost hC hCc hG hGc
        Cells.SystemsPhase.sysP_spec Cells.SystemsPhase.sysCost_cls)))
    (WorkerArith.workerSupply hSU) hR

end NearCubicGates.Close

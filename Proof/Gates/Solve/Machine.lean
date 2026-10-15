import Proof.Gates.Solve.Cost

set_option autoImplicit false

namespace NearCubicGates.Close.Solve

open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord solveWord SolveMachine)

noncomputable def solveMachine : SolveMachine where
  solve := solve
  sound := fun s F h => solve_sound s F h
  complete := fun s h F => solve_complete s h F
  budget := mainCost
  wf := NearCubicGates.Close.Interfaces.wordFunction_of_wmx mainP sOUT (by decide) (fun s => capT (sysWord s).length)
    (fun s => main_run s)
  cls := ⟨costK, 14, mainCost_le⟩

end NearCubicGates.Close.Solve

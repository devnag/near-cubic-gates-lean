import Proof.Gates.Main.FinalOf
import Proof.Gates.CellsConst.Main
import Proof.Gates.CellsGather.Close
import Proof.Gates.CellsGatherQ.QDone
import Proof.Gates.Setup.Supply
import Proof.Gates.Recovery.AfterFinal
import Proof.Gates.Setup.CompU
import Proof.Gates.ENP.TableStage
import Proof.Gates.Succinct.SubstitutionReady

/-!
# The main theorem

`main_from_inputs : FinalStatement`: the nine published inputs (the fields of `NineInputs`, each defined in
`Statement.lean`) imply `NearCubicGates.Target.MainStatement`, the paper's main theorem (`thm:main`,
`paper/paper.tex`). `Solution.lean` gives this theorem to comparator; `Check.lean` prints it with its axioms.
-/

set_option autoImplicit false

namespace NearCubicGates.Close

/-- **The main theorem from the two remaining supplies.** -/
theorem main_of_supplies (hSU : Setup.SetupSupply) (hA : Recovery.AfterSupply) : FinalStatement :=
  main_of_fragments CellsConst.constP (Cells.GatherPhase.gatherPQ Cells.QueryPass.qP) CellsConst.constCost
    (Cells.GatherPhase.gatherCostQ Cells.QueryPass.qCost) CellsConst.constP_spec CellsConst.constP_class
    (Cells.GatherPhase.gatherPQ_spec _ _ Cells.QueryPass.qP_spec) (Cells.GatherPhase.gatherCostQ_class _ Cells.QueryPass.qP_class) hSU
    (Recovery.Common.recoverySupply_of hA)

/-- **The main theorem from the two remaining producers**: the stage-2 SAT program of the `E^NP` recovery
(`ENP.TStageRuns`, paper §11.6 "a formula with one variable per oracle address … finds the first oracle `O*`") and the
composite of the weak machine's set-up (`Setup.CompU`, paper §11.4 "Apply imp:three-pcpp" to `D_B`). -/
theorem main_of_two (hT : ENP.TStageRuns) (hC : ∀ s P, Setup.CompU s P) : FinalStatement :=
  main_of_supplies (Setup.setupSupply_of hC) (Recovery.afterSupply_of hT hC)

theorem main_of_substReady (h : Succinct.SubstMachine.SubstReadySpec) : FinalStatement :=
  main_of_two ENP.tStageRuns (Setup.compU_of h)

/-- **The main theorem.** The nine published inputs imply the paper's main theorem (paper thm:main;
`FinalStatement` in `Close.Statement`). -/
theorem main_from_inputs : FinalStatement :=
  main_of_substReady Succinct.SubstMachine.substReady

end NearCubicGates.Close

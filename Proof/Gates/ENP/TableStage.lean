import Proof.Gates.ENP.TableEmitProg
import Proof.Gates.ENP.TableStageMachine
import Proof.Gates.ENP.TableSearchMeaning
import Proof.Gates.ENP.TableSeedsCost
import Proof.Gates.ENP.TableBytes
import Proof.Gates.ENP.TablePrologueEpilogueCost

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

theorem tStageRuns_of (hPE : TEmit.PECostPoly) : TStageRuns :=
  TableSearch.tStageOf (TEmit.tProgOf_of (TEmit.seedsRuns_of tBytesSpec TableSearch.seedsCostPoly) tBytesSpec hPE)
    TableSearch.tFlagSpec TableSearch.tTableSpec

/-- **Stage 2 of the E^NP recovery** (`sec:all-lengths`): the first honest oracle table of the oracle circuit `C`
(`TStage`: flag `∃ honest table`, the first one framed), by SAT prefix self-reduction on builder T's circuit `c_T`. -/
theorem tStageRuns : TStageRuns := tStageRuns_of TableSearch.pECostPoly

end NearCubicGates.Close.ENP

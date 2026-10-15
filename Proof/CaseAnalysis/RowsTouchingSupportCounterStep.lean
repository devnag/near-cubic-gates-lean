import Proof.CaseAnalysis.RowsTouchingSupportFold
import Proof.MachineModel.Runs

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_step (pre tail : List Bool) (xs : List Cell):
    Step machine (2*xs.length+1) ![pre.length,0,0,0,1,0,0]
      ![pre++frame (xs.map Prod.fst)++tail,(masks xs) 0,(masks xs) 1,(masks xs) 2,[false],[false],[false]]
      ![pre.length+2*xs.length+1,xs.length,xs.length,xs.length,1+count xs,0,0]
      ![pre++frame (xs.map Prod.fst)++tail,(masks xs) 0,(masks xs) 1,(masks xs) 2,
        CompareMachine.word (count xs),[xs.any touched],[xs.any current]]:=by
  obtain ⟨r,hr,hf,hs⟩:=counter_run pre xs tail
  refine ⟨r,hr,?_,?_,hs.le⟩
  · rw [hf];rfl
  · rw [hf];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
